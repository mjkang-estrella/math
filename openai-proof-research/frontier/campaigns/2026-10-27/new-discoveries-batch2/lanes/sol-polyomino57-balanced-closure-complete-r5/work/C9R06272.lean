import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06272G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6272_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r6272targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r6272choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6272targets [(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r6272choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6272targets, c9r6272choice, ?_, checked⟩
    intro S h
    simp only [c9r6272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 18 _ (by rfl)
  have c9r6273_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r6273targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r6273choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6273targets [(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r6273choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6273targets, c9r6273choice, ?_, checked⟩
    intro S h
    simp only [c9r6273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 20 _ (by rfl)
  have c9r6274_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r6274targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r6274choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6274targets [(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r6274choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6274targets, c9r6274choice, ?_, checked⟩
    intro S h
    simp only [c9r6274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 26 _ (by rfl)
  have c9r6275_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r6275targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,4),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6275choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6275targets [(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r6275choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6275targets, c9r6275choice, ?_, checked⟩
    intro S h
    simp only [c9r6275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 3 _ (by rfl)
  have c9r6276_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r6276targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r6276choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r6276targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] c9r6276choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6276targets, c9r6276choice, ?_, checked⟩
    intro S h
    simp only [c9r6276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 12 _ (by rfl)
  have c9r6277_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)] := by
    let c9r6277targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(5,0)]]
    let c9r6277choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6277targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)] c9r6277choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6277targets, c9r6277choice, ?_, checked⟩
    intro S h
    simp only [c9r6277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 17 _ (by rfl)
  have c9r6278_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)] := by
    let c9r6278targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)]]
    let c9r6278choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6278targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)] c9r6278choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6278targets, c9r6278choice, ?_, checked⟩
    intro S h
    simp only [c9r6278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 21 _ (by rfl)
  have c9r6279_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r6279targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r6279choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6279targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)] c9r6279choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6279targets, c9r6279choice, ?_, checked⟩
    intro S h
    simp only [c9r6279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6272_closed
  · subst row; exact c9r6273_closed
  · subst row; exact c9r6274_closed
  · subst row; exact c9r6275_closed
  · subst row; exact c9r6276_closed
  · subst row; exact c9r6277_closed
  · subst row; exact c9r6278_closed
  · subst row; exact c9r6279_closed
theorem C9R06272G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6280_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r6280targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r6280choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6280targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)] c9r6280choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6280targets, c9r6280choice, ?_, checked⟩
    intro S h
    simp only [c9r6280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 26 _ (by rfl)
  have c9r6281_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r6281targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r6281choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6281targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)] c9r6281choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6281targets, c9r6281choice, ?_, checked⟩
    intro S h
    simp only [c9r6281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 28 _ (by rfl)
  have c9r6282_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r6282targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r6282choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6282targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r6282choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6282targets, c9r6282choice, ?_, checked⟩
    intro S h
    simp only [c9r6282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 0 _ (by rfl)
  have c9r6283_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)] := by
    let c9r6283targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,2)]]
    let c9r6283choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6283targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)] c9r6283choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6283targets, c9r6283choice, ?_, checked⟩
    intro S h
    simp only [c9r6283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 3 _ (by rfl)
  have c9r6284_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)] := by
    let c9r6284targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,3)]]
    let c9r6284choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6284targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)] c9r6284choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6284targets, c9r6284choice, ?_, checked⟩
    intro S h
    simp only [c9r6284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 6 _ (by rfl)
  have c9r6285_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)] := by
    let c9r6285targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(6,0)]]
    let c9r6285choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6285targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)] c9r6285choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6285targets, c9r6285choice, ?_, checked⟩
    intro S h
    simp only [c9r6285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 8 _ (by rfl)
  have c9r6286_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r6286targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r6286choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6286targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)] c9r6286choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6286targets, c9r6286choice, ?_, checked⟩
    intro S h
    simp only [c9r6286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 11 _ (by rfl)
  have c9r6287_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)] := by
    let c9r6287targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)]]
    let c9r6287choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6287targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)] c9r6287choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6287targets, c9r6287choice, ?_, checked⟩
    intro S h
    simp only [c9r6287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6280_closed
  · subst row; exact c9r6281_closed
  · subst row; exact c9r6282_closed
  · subst row; exact c9r6283_closed
  · subst row; exact c9r6284_closed
  · subst row; exact c9r6285_closed
  · subst row; exact c9r6286_closed
  · subst row; exact c9r6287_closed
theorem C9R06272G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6288_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)] := by
    let c9r6288targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)]]
    let c9r6288choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6288targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)] c9r6288choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6288targets, c9r6288choice, ?_, checked⟩
    intro S h
    simp only [c9r6288targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 17 _ (by rfl)
  have c9r6289_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)] := by
    let c9r6289targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)]]
    let c9r6289choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6289targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)] c9r6289choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6289targets, c9r6289choice, ?_, checked⟩
    intro S h
    simp only [c9r6289targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 20 _ (by rfl)
  have c9r6290_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)] := by
    let c9r6290targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)]]
    let c9r6290choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6290targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)] c9r6290choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6290targets, c9r6290choice, ?_, checked⟩
    intro S h
    simp only [c9r6290targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 23 _ (by rfl)
  have c9r6291_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)] := by
    let c9r6291targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,4)]]
    let c9r6291choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6291targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)] c9r6291choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6291targets, c9r6291choice, ?_, checked⟩
    intro S h
    simp only [c9r6291targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 26 _ (by rfl)
  have c9r6292_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)] := by
    let c9r6292targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3),(6,3)]]
    let c9r6292choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6292targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)] c9r6292choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6292targets, c9r6292choice, ?_, checked⟩
    intro S h
    simp only [c9r6292targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 29 _ (by rfl)
  have c9r6293_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r6293targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6293choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6293targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)] c9r6293choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6293targets, c9r6293choice, ?_, checked⟩
    intro S h
    simp only [c9r6293targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 2 _ (by rfl)
  have c9r6294_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c9r6294targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c9r6294choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6294targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)] c9r6294choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6294targets, c9r6294choice, ?_, checked⟩
    intro S h
    simp only [c9r6294targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 4 _ (by rfl)
  have c9r6295_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c9r6295targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c9r6295choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6295targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)] c9r6295choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6295targets, c9r6295choice, ?_, checked⟩
    intro S h
    simp only [c9r6295targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6288_closed
  · subst row; exact c9r6289_closed
  · subst row; exact c9r6290_closed
  · subst row; exact c9r6291_closed
  · subst row; exact c9r6292_closed
  · subst row; exact c9r6293_closed
  · subst row; exact c9r6294_closed
  · subst row; exact c9r6295_closed
theorem C9R06272G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6296_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)] := by
    let c9r6296targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,3)]]
    let c9r6296choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6296targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)] c9r6296choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6296targets, c9r6296choice, ?_, checked⟩
    intro S h
    simp only [c9r6296targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 10 _ (by rfl)
  have c9r6297_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)] := by
    let c9r6297targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(6,0)]]
    let c9r6297choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6297targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)] c9r6297choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6297targets, c9r6297choice, ?_, checked⟩
    intro S h
    simp only [c9r6297targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 13 _ (by rfl)
  have c9r6298_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)] := by
    let c9r6298targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2),(6,2)]]
    let c9r6298choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6298targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)] c9r6298choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6298targets, c9r6298choice, ?_, checked⟩
    intro S h
    simp only [c9r6298targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 16 _ (by rfl)
  have c9r6299_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)] := by
    let c9r6299targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,1)]]
    let c9r6299choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6299targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)] c9r6299choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6299targets, c9r6299choice, ?_, checked⟩
    intro S h
    simp only [c9r6299targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 19 _ (by rfl)
  have c9r6300_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)] := by
    let c9r6300targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0),(7,0)]]
    let c9r6300choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6300targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)] c9r6300choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6300targets, c9r6300choice, ?_, checked⟩
    intro S h
    simp only [c9r6300targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 21 _ (by rfl)
  have c9r6301_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)] := by
    let c9r6301targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)]]
    let c9r6301choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6301targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)] c9r6301choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6301targets, c9r6301choice, ?_, checked⟩
    intro S h
    simp only [c9r6301targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 25 _ (by rfl)
  have c9r6302_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)] := by
    let c9r6302targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)]]
    let c9r6302choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6302targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)] c9r6302choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6302targets, c9r6302choice, ?_, checked⟩
    intro S h
    simp only [c9r6302targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 28 _ (by rfl)
  have c9r6303_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)] := by
    let c9r6303targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)]]
    let c9r6303choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6303targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)] c9r6303choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6303targets, c9r6303choice, ?_, checked⟩
    intro S h
    simp only [c9r6303targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6296_closed
  · subst row; exact c9r6297_closed
  · subst row; exact c9r6298_closed
  · subst row; exact c9r6299_closed
  · subst row; exact c9r6300_closed
  · subst row; exact c9r6301_closed
  · subst row; exact c9r6302_closed
  · subst row; exact c9r6303_closed
theorem C9R06272_closed (row : List GridPoint) (h : FamilyMember row F9B003L4) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L4, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06272G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06272G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06272G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06272G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06272G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06272G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06272G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06272G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06272G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06272G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06272G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06272G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06272G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06272G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06272G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06272G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06272G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06272G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06272G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06272G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06272G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06272G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06272G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06272G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06272G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06272G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06272G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06272G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06272G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06272G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06272G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06272G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
