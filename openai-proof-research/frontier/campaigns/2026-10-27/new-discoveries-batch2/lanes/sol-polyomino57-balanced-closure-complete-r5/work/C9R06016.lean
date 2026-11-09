import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06016G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6016_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)] := by
    let c9r6016targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(5,1)]]
    let c9r6016choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6016targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)] c9r6016choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6016targets, c9r6016choice, ?_, checked⟩
    intro S h
    simp only [c9r6016targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 27 _ (by rfl)
  have c9r6017_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)] := by
    let c9r6017targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(5,3)]]
    let c9r6017choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6017targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)] c9r6017choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6017targets, c9r6017choice, ?_, checked⟩
    intro S h
    simp only [c9r6017targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 30 _ (by rfl)
  have c9r6018_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] := by
    let c9r6018targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)]]
    let c9r6018choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6018targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] c9r6018choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6018targets, c9r6018choice, ?_, checked⟩
    intro S h
    simp only [c9r6018targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 1 _ (by rfl)
  have c9r6019_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)] := by
    let c9r6019targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,2)]]
    let c9r6019choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6019targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)] c9r6019choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6019targets, c9r6019choice, ?_, checked⟩
    intro S h
    simp only [c9r6019targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 4 _ (by rfl)
  have c9r6020_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)] := by
    let c9r6020targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(6,1)]]
    let c9r6020choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6020targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)] c9r6020choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6020targets, c9r6020choice, ?_, checked⟩
    intro S h
    simp only [c9r6020targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 7 _ (by rfl)
  have c9r6021_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)] := by
    let c9r6021targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6021choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6021targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)] c9r6021choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6021targets, c9r6021choice, ?_, checked⟩
    intro S h
    simp only [c9r6021targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 11 _ (by rfl)
  have c9r6022_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)] := by
    let c9r6022targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)]]
    let c9r6022choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6022targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)] c9r6022choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6022targets, c9r6022choice, ?_, checked⟩
    intro S h
    simp only [c9r6022targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 14 _ (by rfl)
  have c9r6023_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)] := by
    let c9r6023targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)]]
    let c9r6023choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6023targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)] c9r6023choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6023targets, c9r6023choice, ?_, checked⟩
    intro S h
    simp only [c9r6023targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6016_closed
  · subst row; exact c9r6017_closed
  · subst row; exact c9r6018_closed
  · subst row; exact c9r6019_closed
  · subst row; exact c9r6020_closed
  · subst row; exact c9r6021_closed
  · subst row; exact c9r6022_closed
  · subst row; exact c9r6023_closed
theorem C9R06016G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6024_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)] := by
    let c9r6024targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)]]
    let c9r6024choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6024targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)] c9r6024choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6024targets, c9r6024choice, ?_, checked⟩
    intro S h
    simp only [c9r6024targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 20 _ (by rfl)
  have c9r6025_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)] := by
    let c9r6025targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)]]
    let c9r6025choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6025targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)] c9r6025choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6025targets, c9r6025choice, ?_, checked⟩
    intro S h
    simp only [c9r6025targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 23 _ (by rfl)
  have c9r6026_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)] := by
    let c9r6026targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)]]
    let c9r6026choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6026targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)] c9r6026choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6026targets, c9r6026choice, ?_, checked⟩
    intro S h
    simp only [c9r6026targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 26 _ (by rfl)
  have c9r6027_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)] := by
    let c9r6027targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)]]
    let c9r6027choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6027targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)] c9r6027choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6027targets, c9r6027choice, ?_, checked⟩
    intro S h
    simp only [c9r6027targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 30 _ (by rfl)
  have c9r6028_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)] := by
    let c9r6028targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)]]
    let c9r6028choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6028targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)] c9r6028choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6028targets, c9r6028choice, ?_, checked⟩
    intro S h
    simp only [c9r6028targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 1 _ (by rfl)
  have c9r6029_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)] := by
    let c9r6029targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)]]
    let c9r6029choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6029targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)] c9r6029choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6029targets, c9r6029choice, ?_, checked⟩
    intro S h
    simp only [c9r6029targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 3 _ (by rfl)
  have c9r6030_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)] := by
    let c9r6030targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)]]
    let c9r6030choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6030targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)] c9r6030choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6030targets, c9r6030choice, ?_, checked⟩
    intro S h
    simp only [c9r6030targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 7 _ (by rfl)
  have c9r6031_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)] := by
    let c9r6031targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)]]
    let c9r6031choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6031targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)] c9r6031choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6031targets, c9r6031choice, ?_, checked⟩
    intro S h
    simp only [c9r6031targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6024_closed
  · subst row; exact c9r6025_closed
  · subst row; exact c9r6026_closed
  · subst row; exact c9r6027_closed
  · subst row; exact c9r6028_closed
  · subst row; exact c9r6029_closed
  · subst row; exact c9r6030_closed
  · subst row; exact c9r6031_closed
theorem C9R06016G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6032_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)] := by
    let c9r6032targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)]]
    let c9r6032choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6032targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)] c9r6032choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6032targets, c9r6032choice, ?_, checked⟩
    intro S h
    simp only [c9r6032targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 13 _ (by rfl)
  have c9r6033_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)] := by
    let c9r6033targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,0),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6033choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6033targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)] c9r6033choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6033targets, c9r6033choice, ?_, checked⟩
    intro S h
    simp only [c9r6033targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 20 _ (by rfl)
  have c9r6034_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r6034targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r6034choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6034targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r6034choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6034targets, c9r6034choice, ?_, checked⟩
    intro S h
    simp only [c9r6034targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 26 _ (by rfl)
  have c9r6035_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r6035targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r6035choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6035targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r6035choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6035targets, c9r6035choice, ?_, checked⟩
    intro S h
    simp only [c9r6035targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 29 _ (by rfl)
  have c9r6036_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r6036targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r6036choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6036targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r6036choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6036targets, c9r6036choice, ?_, checked⟩
    intro S h
    simp only [c9r6036targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 31 _ (by rfl)
  have c9r6037_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r6037targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r6037choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6037targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r6037choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6037targets, c9r6037choice, ?_, checked⟩
    intro S h
    simp only [c9r6037targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 1 _ (by rfl)
  have c9r6038_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r6038targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r6038choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6038targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] c9r6038choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6038targets, c9r6038choice, ?_, checked⟩
    intro S h
    simp only [c9r6038targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 4 _ (by rfl)
  have c9r6039_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r6039targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r6039choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6039targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] c9r6039choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6039targets, c9r6039choice, ?_, checked⟩
    intro S h
    simp only [c9r6039targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6032_closed
  · subst row; exact c9r6033_closed
  · subst row; exact c9r6034_closed
  · subst row; exact c9r6035_closed
  · subst row; exact c9r6036_closed
  · subst row; exact c9r6037_closed
  · subst row; exact c9r6038_closed
  · subst row; exact c9r6039_closed
theorem C9R06016G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6040_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r6040targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r6040choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6040targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] c9r6040choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6040targets, c9r6040choice, ?_, checked⟩
    intro S h
    simp only [c9r6040targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 9 _ (by rfl)
  have c9r6041_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r6041targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r6041choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6041targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] c9r6041choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6041targets, c9r6041choice, ?_, checked⟩
    intro S h
    simp only [c9r6041targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 12 _ (by rfl)
  have c9r6042_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)] := by
    let c9r6042targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,0),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6042choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6042targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)] c9r6042choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6042targets, c9r6042choice, ?_, checked⟩
    intro S h
    simp only [c9r6042targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 17 _ (by rfl)
  have c9r6043_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)] := by
    let c9r6043targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(5,0)]]
    let c9r6043choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6043targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)] c9r6043choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6043targets, c9r6043choice, ?_, checked⟩
    intro S h
    simp only [c9r6043targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 21 _ (by rfl)
  have c9r6044_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)] := by
    let c9r6044targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2),(5,2)]]
    let c9r6044choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6044targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)] c9r6044choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6044targets, c9r6044choice, ?_, checked⟩
    intro S h
    simp only [c9r6044targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 24 _ (by rfl)
  have c9r6045_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)] := by
    let c9r6045targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3),(5,3)]]
    let c9r6045choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6045targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)] c9r6045choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6045targets, c9r6045choice, ?_, checked⟩
    intro S h
    simp only [c9r6045targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 26 _ (by rfl)
  have c9r6046_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)] := by
    let c9r6046targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(5,1)]]
    let c9r6046choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6046targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)] c9r6046choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6046targets, c9r6046choice, ?_, checked⟩
    intro S h
    simp only [c9r6046targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 29 _ (by rfl)
  have c9r6047_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)] := by
    let c9r6047targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2),(5,2)]]
    let c9r6047choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6047targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)] c9r6047choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6047targets, c9r6047choice, ?_, checked⟩
    intro S h
    simp only [c9r6047targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6040_closed
  · subst row; exact c9r6041_closed
  · subst row; exact c9r6042_closed
  · subst row; exact c9r6043_closed
  · subst row; exact c9r6044_closed
  · subst row; exact c9r6045_closed
  · subst row; exact c9r6046_closed
  · subst row; exact c9r6047_closed
theorem C9R06016_closed (row : List GridPoint) (h : FamilyMember row F9B002L60) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L60, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06016G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06016G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06016G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06016G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06016G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06016G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06016G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06016G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06016G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06016G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06016G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06016G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06016G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06016G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06016G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06016G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06016G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06016G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06016G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06016G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06016G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06016G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06016G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06016G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06016G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06016G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06016G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06016G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06016G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06016G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06016G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06016G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
