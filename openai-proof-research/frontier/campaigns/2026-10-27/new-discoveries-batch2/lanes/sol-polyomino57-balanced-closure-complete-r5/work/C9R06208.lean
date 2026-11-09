import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06208G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6208_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r6208targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r6208choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6208targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)] c9r6208choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6208targets, c9r6208choice, ?_, checked⟩
    intro S h
    simp only [c9r6208targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 10 _ (by rfl)
  have c9r6209_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r6209targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0),(5,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r6209choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6209targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)] c9r6209choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6209targets, c9r6209choice, ?_, checked⟩
    intro S h
    simp only [c9r6209targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 12 _ (by rfl)
  have c9r6210_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r6210targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r6210choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6210targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)] c9r6210choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6210targets, c9r6210choice, ?_, checked⟩
    intro S h
    simp only [c9r6210targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 15 _ (by rfl)
  have c9r6211_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r6211targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r6211choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6211targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)] c9r6211choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6211targets, c9r6211choice, ?_, checked⟩
    intro S h
    simp only [c9r6211targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 18 _ (by rfl)
  have c9r6212_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r6212targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r6212choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6212targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] c9r6212choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6212targets, c9r6212choice, ?_, checked⟩
    intro S h
    simp only [c9r6212targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 23 _ (by rfl)
  have c9r6213_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)] := by
    let c9r6213targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,1)]]
    let c9r6213choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6213targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)] c9r6213choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6213targets, c9r6213choice, ?_, checked⟩
    intro S h
    simp only [c9r6213targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 29 _ (by rfl)
  have c9r6214_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r6214targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6214choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6214targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)] c9r6214choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6214targets, c9r6214choice, ?_, checked⟩
    intro S h
    simp only [c9r6214targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 2 _ (by rfl)
  have c9r6215_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r6215targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r6215choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6215targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)] c9r6215choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6215targets, c9r6215choice, ?_, checked⟩
    intro S h
    simp only [c9r6215targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6208_closed
  · subst row; exact c9r6209_closed
  · subst row; exact c9r6210_closed
  · subst row; exact c9r6211_closed
  · subst row; exact c9r6212_closed
  · subst row; exact c9r6213_closed
  · subst row; exact c9r6214_closed
  · subst row; exact c9r6215_closed
theorem C9R06208G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6216_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r6216targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r6216choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6216targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)] c9r6216choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6216targets, c9r6216choice, ?_, checked⟩
    intro S h
    simp only [c9r6216targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 6 _ (by rfl)
  have c9r6217_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r6217targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r6217choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6217targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)] c9r6217choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6217targets, c9r6217choice, ?_, checked⟩
    intro S h
    simp only [c9r6217targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 10 _ (by rfl)
  have c9r6218_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r6218targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6218choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6218targets [(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] c9r6218choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6218targets, c9r6218choice, ?_, checked⟩
    intro S h
    simp only [c9r6218targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 16 _ (by rfl)
  have c9r6219_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r6219targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6219choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6219targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r6219choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6219targets, c9r6219choice, ?_, checked⟩
    intro S h
    simp only [c9r6219targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 26 _ (by rfl)
  have c9r6220_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r6220targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r6220choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6220targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r6220choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6220targets, c9r6220choice, ?_, checked⟩
    intro S h
    simp only [c9r6220targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 30 _ (by rfl)
  have c9r6221_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r6221targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r6221choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6221targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r6221choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6221targets, c9r6221choice, ?_, checked⟩
    intro S h
    simp only [c9r6221targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 1 _ (by rfl)
  have c9r6222_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r6222targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r6222choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6222targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r6222choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6222targets, c9r6222choice, ?_, checked⟩
    intro S h
    simp only [c9r6222targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 3 _ (by rfl)
  have c9r6223_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r6223targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r6223choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6223targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r6223choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6223targets, c9r6223choice, ?_, checked⟩
    intro S h
    simp only [c9r6223targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6216_closed
  · subst row; exact c9r6217_closed
  · subst row; exact c9r6218_closed
  · subst row; exact c9r6219_closed
  · subst row; exact c9r6220_closed
  · subst row; exact c9r6221_closed
  · subst row; exact c9r6222_closed
  · subst row; exact c9r6223_closed
theorem C9R06208G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6224_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r6224targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r6224choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6224targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r6224choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6224targets, c9r6224choice, ?_, checked⟩
    intro S h
    simp only [c9r6224targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 8 _ (by rfl)
  have c9r6225_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r6225targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r6225choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6225targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r6225choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6225targets, c9r6225choice, ?_, checked⟩
    intro S h
    simp only [c9r6225targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 11 _ (by rfl)
  have c9r6226_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r6226targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r6226choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6226targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r6226choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6226targets, c9r6226choice, ?_, checked⟩
    intro S h
    simp only [c9r6226targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 13 _ (by rfl)
  have c9r6227_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r6227targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r6227choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6227targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r6227choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6227targets, c9r6227choice, ?_, checked⟩
    intro S h
    simp only [c9r6227targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 16 _ (by rfl)
  have c9r6228_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r6228targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r6228choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6228targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r6228choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6228targets, c9r6228choice, ?_, checked⟩
    intro S h
    simp only [c9r6228targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 19 _ (by rfl)
  have c9r6229_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r6229targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r6229choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6229targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r6229choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6229targets, c9r6229choice, ?_, checked⟩
    intro S h
    simp only [c9r6229targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 22 _ (by rfl)
  have c9r6230_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r6230targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r6230choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6230targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r6230choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6230targets, c9r6230choice, ?_, checked⟩
    intro S h
    simp only [c9r6230targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 25 _ (by rfl)
  have c9r6231_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r6231targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6231choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6231targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)] c9r6231choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6231targets, c9r6231choice, ?_, checked⟩
    intro S h
    simp only [c9r6231targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6224_closed
  · subst row; exact c9r6225_closed
  · subst row; exact c9r6226_closed
  · subst row; exact c9r6227_closed
  · subst row; exact c9r6228_closed
  · subst row; exact c9r6229_closed
  · subst row; exact c9r6230_closed
  · subst row; exact c9r6231_closed
theorem C9R06208G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6232_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r6232targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r6232choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6232targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)] c9r6232choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6232targets, c9r6232choice, ?_, checked⟩
    intro S h
    simp only [c9r6232targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 0 _ (by rfl)
  have c9r6233_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r6233targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r6233choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6233targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)] c9r6233choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6233targets, c9r6233choice, ?_, checked⟩
    intro S h
    simp only [c9r6233targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 2 _ (by rfl)
  have c9r6234_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)] := by
    let c9r6234targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)]]
    let c9r6234choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6234targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)] c9r6234choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6234targets, c9r6234choice, ?_, checked⟩
    intro S h
    simp only [c9r6234targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 5 _ (by rfl)
  have c9r6235_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)] := by
    let c9r6235targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)]]
    let c9r6235choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6235targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)] c9r6235choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6235targets, c9r6235choice, ?_, checked⟩
    intro S h
    simp only [c9r6235targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 7 _ (by rfl)
  have c9r6236_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r6236targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r6236choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6236targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)] c9r6236choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6236targets, c9r6236choice, ?_, checked⟩
    intro S h
    simp only [c9r6236targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 11 _ (by rfl)
  have c9r6237_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r6237targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r6237choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6237targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)] c9r6237choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6237targets, c9r6237choice, ?_, checked⟩
    intro S h
    simp only [c9r6237targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 14 _ (by rfl)
  have c9r6238_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r6238targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r6238choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6238targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)] c9r6238choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6238targets, c9r6238choice, ?_, checked⟩
    intro S h
    simp only [c9r6238targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 16 _ (by rfl)
  have c9r6239_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r6239targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r6239choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6239targets [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)] c9r6239choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6239targets, c9r6239choice, ?_, checked⟩
    intro S h
    simp only [c9r6239targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6232_closed
  · subst row; exact c9r6233_closed
  · subst row; exact c9r6234_closed
  · subst row; exact c9r6235_closed
  · subst row; exact c9r6236_closed
  · subst row; exact c9r6237_closed
  · subst row; exact c9r6238_closed
  · subst row; exact c9r6239_closed
theorem C9R06208_closed (row : List GridPoint) (h : FamilyMember row F9B003L2) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L2, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06208G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06208G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06208G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06208G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06208G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06208G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06208G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06208G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06208G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06208G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06208G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06208G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06208G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06208G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06208G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06208G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06208G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06208G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06208G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06208G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06208G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06208G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06208G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06208G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06208G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06208G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06208G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06208G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06208G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06208G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06208G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06208G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
