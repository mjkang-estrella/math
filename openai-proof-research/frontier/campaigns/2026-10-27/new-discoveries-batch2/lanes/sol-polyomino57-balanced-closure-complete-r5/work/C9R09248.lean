import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R09248G0 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9248_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r9248targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1),(4,2)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r9248choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9248targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)] c9r9248choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9248targets, c9r9248choice, ?_, checked⟩
    intro S h
    simp only [c9r9248targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 27 _ (by rfl)
  have c9r9249_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r9249targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1),(5,1)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r9249choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9249targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)] c9r9249choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9249targets, c9r9249choice, ?_, checked⟩
    intro S h
    simp only [c9r9249targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 30 _ (by rfl)
  have c9r9250_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r9250targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r9250choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9250targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] c9r9250choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9250targets, c9r9250choice, ?_, checked⟩
    intro S h
    simp only [c9r9250targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
  have c9r9251_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)] := by
    let c9r9251targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(4,3),(5,0),(5,1)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,0),(4,1)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,2),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,1)]]
    let c9r9251choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9251targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)] c9r9251choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9251targets, c9r9251choice, ?_, checked⟩
    intro S h
    simp only [c9r9251targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 9 _ (by rfl)
  have c9r9252_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r9252targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r9252choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9252targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)] c9r9252choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9252targets, c9r9252choice, ?_, checked⟩
    intro S h
    simp only [c9r9252targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 14 _ (by rfl)
  have c9r9253_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r9253targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,0)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,0)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r9253choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9253targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)] c9r9253choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9253targets, c9r9253choice, ?_, checked⟩
    intro S h
    simp only [c9r9253targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 16 _ (by rfl)
  have c9r9254_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r9254targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,1)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,1)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r9254choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9254targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)] c9r9254choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9254targets, c9r9254choice, ?_, checked⟩
    intro S h
    simp only [c9r9254targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 18 _ (by rfl)
  have c9r9255_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r9255targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,1),(6,0),(6,1)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r9255choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9255targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)] c9r9255choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9255targets, c9r9255choice, ?_, checked⟩
    intro S h
    simp only [c9r9255targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9248_closed
  · subst row; exact c9r9249_closed
  · subst row; exact c9r9250_closed
  · subst row; exact c9r9251_closed
  · subst row; exact c9r9252_closed
  · subst row; exact c9r9253_closed
  · subst row; exact c9r9254_closed
  · subst row; exact c9r9255_closed
theorem C9R09248G1 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9256_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r9256targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r9256choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9256targets [(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] c9r9256choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9256targets, c9r9256choice, ?_, checked⟩
    intro S h
    simp only [c9r9256targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
  have c9r9257_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9257targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,4),(2,2),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9257choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9257targets [(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)] c9r9257choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9257targets, c9r9257choice, ?_, checked⟩
    intro S h
    simp only [c9r9257targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 5 _ (by rfl)
  have c9r9258_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r9258targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r9258choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9258targets [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r9258choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9258targets, c9r9258choice, ?_, checked⟩
    intro S h
    simp only [c9r9258targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 12 _ (by rfl)
  have c9r9259_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r9259targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,4),(1,4),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r9259choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9259targets [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r9259choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9259targets, c9r9259choice, ?_, checked⟩
    intro S h
    simp only [c9r9259targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
  have c9r9260_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r9260targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,4),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r9260choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9260targets [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r9260choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9260targets, c9r9260choice, ?_, checked⟩
    intro S h
    simp only [c9r9260targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
  have c9r9261_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r9261targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,4),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r9261choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9261targets [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r9261choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9261targets, c9r9261choice, ?_, checked⟩
    intro S h
    simp only [c9r9261targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 21 _ (by rfl)
  have c9r9262_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r9262targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,4),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r9262choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9262targets [(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r9262choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9262targets, c9r9262choice, ?_, checked⟩
    intro S h
    simp only [c9r9262targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 23 _ (by rfl)
  have c9r9263_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r9263targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(1,4),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,4),(1,4),(2,2),(2,4),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r9263choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9263targets [(0,3),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r9263choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9263targets, c9r9263choice, ?_, checked⟩
    intro S h
    simp only [c9r9263targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9256_closed
  · subst row; exact c9r9257_closed
  · subst row; exact c9r9258_closed
  · subst row; exact c9r9259_closed
  · subst row; exact c9r9260_closed
  · subst row; exact c9r9261_closed
  · subst row; exact c9r9262_closed
  · subst row; exact c9r9263_closed
theorem C9R09248G2 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9264_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)] := by
    let c9r9264targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,0),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2)],[(0,4),(1,4),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,4)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,5)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,2)]]
    let c9r9264choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9264targets [(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)] c9r9264choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9264targets, c9r9264choice, ?_, checked⟩
    intro S h
    simp only [c9r9264targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 6 _ (by rfl)
  have c9r9265_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9265targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,4),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9265choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9265targets [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)] c9r9265choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9265targets, c9r9265choice, ?_, checked⟩
    intro S h
    simp only [c9r9265targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
  have c9r9266_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)] := by
    let c9r9266targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,4)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,3),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,4)],[(0,4),(1,4),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,5)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(3,5)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,4)]]
    let c9r9266choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9266targets [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)] c9r9266choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9266targets, c9r9266choice, ?_, checked⟩
    intro S h
    simp only [c9r9266targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 18 _ (by rfl)
  have c9r9267_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r9267targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,4),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,0)],[(0,4),(1,4),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r9267choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9267targets [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)] c9r9267choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9267targets, c9r9267choice, ?_, checked⟩
    intro S h
    simp only [c9r9267targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 21 _ (by rfl)
  have c9r9268_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r9268targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,1)],[(0,4),(1,4),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r9268choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9268targets [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)] c9r9268choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9268targets, c9r9268choice, ?_, checked⟩
    intro S h
    simp only [c9r9268targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 23 _ (by rfl)
  have c9r9269_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r9269targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,2)],[(0,4),(1,4),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r9269choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9269targets [(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)] c9r9269choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9269targets, c9r9269choice, ?_, checked⟩
    intro S h
    simp only [c9r9269targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 25 _ (by rfl)
  have c9r9270_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r9270targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4),(4,0),(4,1)],[(0,4),(1,4),(2,3),(2,4),(2,5),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r9270choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9270targets [(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)] c9r9270choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9270targets, c9r9270choice, ?_, checked⟩
    intro S h
    simp only [c9r9270targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 31 _ (by rfl)
  have c9r9271_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r9271targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,0),(4,1),(4,2)],[(0,4),(1,4),(2,3),(2,4),(2,5),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r9271choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9271targets [(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)] c9r9271choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9271targets, c9r9271choice, ?_, checked⟩
    intro S h
    simp only [c9r9271targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9264_closed
  · subst row; exact c9r9265_closed
  · subst row; exact c9r9266_closed
  · subst row; exact c9r9267_closed
  · subst row; exact c9r9268_closed
  · subst row; exact c9r9269_closed
  · subst row; exact c9r9270_closed
  · subst row; exact c9r9271_closed
theorem C9R09248G3 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9272_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r9272targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r9272choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9272targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r9272choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9272targets, c9r9272choice, ?_, checked⟩
    intro S h
    simp only [c9r9272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 15 _ (by rfl)
  have c9r9273_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r9273targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,4),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r9273choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9273targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r9273choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9273targets, c9r9273choice, ?_, checked⟩
    intro S h
    simp only [c9r9273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 19 _ (by rfl)
  have c9r9274_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r9274targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r9274choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9274targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r9274choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9274targets, c9r9274choice, ?_, checked⟩
    intro S h
    simp only [c9r9274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 22 _ (by rfl)
  have c9r9275_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r9275targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r9275choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9275targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r9275choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9275targets, c9r9275choice, ?_, checked⟩
    intro S h
    simp only [c9r9275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 24 _ (by rfl)
  have c9r9276_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r9276targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r9276choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9276targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r9276choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9276targets, c9r9276choice, ?_, checked⟩
    intro S h
    simp only [c9r9276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 26 _ (by rfl)
  have c9r9277_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r9277targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,4),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r9277choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9277targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r9277choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9277targets, c9r9277choice, ?_, checked⟩
    intro S h
    simp only [c9r9277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 29 _ (by rfl)
  have c9r9278_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r9278targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,4),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r9278choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9278targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r9278choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9278targets, c9r9278choice, ?_, checked⟩
    intro S h
    simp only [c9r9278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 0 _ (by rfl)
  have c9r9279_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r9279targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,4),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,4),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r9279choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9279targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r9279choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9279targets, c9r9279choice, ?_, checked⟩
    intro S h
    simp only [c9r9279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9272_closed
  · subst row; exact c9r9273_closed
  · subst row; exact c9r9274_closed
  · subst row; exact c9r9275_closed
  · subst row; exact c9r9276_closed
  · subst row; exact c9r9277_closed
  · subst row; exact c9r9278_closed
  · subst row; exact c9r9279_closed
theorem C9R09248_closed (row : List GridPoint) (h : FamilyMember row F9B004L33) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L33, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R09248G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09248G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09248G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09248G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09248G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09248G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09248G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09248G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09248G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09248G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09248G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09248G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09248G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09248G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09248G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09248G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09248G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09248G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09248G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09248G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09248G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09248G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09248G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09248G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09248G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09248G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09248G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09248G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09248G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09248G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09248G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09248G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
