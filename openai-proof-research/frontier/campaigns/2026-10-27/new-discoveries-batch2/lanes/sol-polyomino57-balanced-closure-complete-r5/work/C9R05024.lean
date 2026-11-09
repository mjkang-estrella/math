import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R05024G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5024_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] := by
    let c9r5024targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)]]
    let c9r5024choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5024targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] c9r5024choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5024targets, c9r5024choice, ?_, checked⟩
    intro S h
    simp only [c9r5024targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 28 _ (by rfl)
  have c9r5025_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)] := by
    let c9r5025targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,2)]]
    let c9r5025choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5025targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)] c9r5025choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5025targets, c9r5025choice, ?_, checked⟩
    intro S h
    simp only [c9r5025targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 31 _ (by rfl)
  have c9r5026_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)] := by
    let c9r5026targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(5,1)]]
    let c9r5026choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5026targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)] c9r5026choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5026targets, c9r5026choice, ?_, checked⟩
    intro S h
    simp only [c9r5026targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 2 _ (by rfl)
  have c9r5027_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)] := by
    let c9r5027targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c9r5027choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5027targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)] c9r5027choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5027targets, c9r5027choice, ?_, checked⟩
    intro S h
    simp only [c9r5027targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 6 _ (by rfl)
  have c9r5028_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)] := by
    let c9r5028targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)]]
    let c9r5028choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5028targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)] c9r5028choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5028targets, c9r5028choice, ?_, checked⟩
    intro S h
    simp only [c9r5028targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 9 _ (by rfl)
  have c9r5029_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)] := by
    let c9r5029targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)]]
    let c9r5029choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5029targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)] c9r5029choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5029targets, c9r5029choice, ?_, checked⟩
    intro S h
    simp only [c9r5029targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 11 _ (by rfl)
  have c9r5030_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)] := by
    let c9r5030targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)]]
    let c9r5030choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5030targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)] c9r5030choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5030targets, c9r5030choice, ?_, checked⟩
    intro S h
    simp only [c9r5030targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 15 _ (by rfl)
  have c9r5031_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)] := by
    let c9r5031targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)]]
    let c9r5031choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5031targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)] c9r5031choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5031targets, c9r5031choice, ?_, checked⟩
    intro S h
    simp only [c9r5031targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5024_closed
  · subst row; exact c9r5025_closed
  · subst row; exact c9r5026_closed
  · subst row; exact c9r5027_closed
  · subst row; exact c9r5028_closed
  · subst row; exact c9r5029_closed
  · subst row; exact c9r5030_closed
  · subst row; exact c9r5031_closed
theorem C9R05024G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5032_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)] := by
    let c9r5032targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)]]
    let c9r5032choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5032targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)] c9r5032choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5032targets, c9r5032choice, ?_, checked⟩
    intro S h
    simp only [c9r5032targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 22 _ (by rfl)
  have c9r5033_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)] := by
    let c9r5033targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)]]
    let c9r5033choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5033targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)] c9r5033choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5033targets, c9r5033choice, ?_, checked⟩
    intro S h
    simp only [c9r5033targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 26 _ (by rfl)
  have c9r5034_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)] := by
    let c9r5034targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)]]
    let c9r5034choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5034targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)] c9r5034choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5034targets, c9r5034choice, ?_, checked⟩
    intro S h
    simp only [c9r5034targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 29 _ (by rfl)
  have c9r5035_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)] := by
    let c9r5035targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)]]
    let c9r5035choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5035targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)] c9r5035choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5035targets, c9r5035choice, ?_, checked⟩
    intro S h
    simp only [c9r5035targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 0 _ (by rfl)
  have c9r5036_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)] := by
    let c9r5036targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)]]
    let c9r5036choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5036targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)] c9r5036choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5036targets, c9r5036choice, ?_, checked⟩
    intro S h
    simp only [c9r5036targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 4 _ (by rfl)
  have c9r5037_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)] := by
    let c9r5037targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)]]
    let c9r5037choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5037targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)] c9r5037choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5037targets, c9r5037choice, ?_, checked⟩
    intro S h
    simp only [c9r5037targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 7 _ (by rfl)
  have c9r5038_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)] := by
    let c9r5038targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)]]
    let c9r5038choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5038targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)] c9r5038choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5038targets, c9r5038choice, ?_, checked⟩
    intro S h
    simp only [c9r5038targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 9 _ (by rfl)
  have c9r5039_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)] := by
    let c9r5039targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)]]
    let c9r5039choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5039targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)] c9r5039choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5039targets, c9r5039choice, ?_, checked⟩
    intro S h
    simp only [c9r5039targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5032_closed
  · subst row; exact c9r5033_closed
  · subst row; exact c9r5034_closed
  · subst row; exact c9r5035_closed
  · subst row; exact c9r5036_closed
  · subst row; exact c9r5037_closed
  · subst row; exact c9r5038_closed
  · subst row; exact c9r5039_closed
theorem C9R05024G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5040_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)] := by
    let c9r5040targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)]]
    let c9r5040choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5040targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)] c9r5040choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5040targets, c9r5040choice, ?_, checked⟩
    intro S h
    simp only [c9r5040targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 16 _ (by rfl)
  have c9r5041_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)] := by
    let c9r5041targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)]]
    let c9r5041choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5041targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)] c9r5041choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5041targets, c9r5041choice, ?_, checked⟩
    intro S h
    simp only [c9r5041targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 19 _ (by rfl)
  have c9r5042_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)] := by
    let c9r5042targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)]]
    let c9r5042choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5042targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)] c9r5042choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5042targets, c9r5042choice, ?_, checked⟩
    intro S h
    simp only [c9r5042targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 23 _ (by rfl)
  have c9r5043_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)] := by
    let c9r5043targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)]]
    let c9r5043choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5043targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)] c9r5043choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5043targets, c9r5043choice, ?_, checked⟩
    intro S h
    simp only [c9r5043targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 26 _ (by rfl)
  have c9r5044_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)] := by
    let c9r5044targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)]]
    let c9r5044choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5044targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)] c9r5044choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5044targets, c9r5044choice, ?_, checked⟩
    intro S h
    simp only [c9r5044targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 28 _ (by rfl)
  have c9r5045_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)] := by
    let c9r5045targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)]]
    let c9r5045choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5045targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)] c9r5045choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5045targets, c9r5045choice, ?_, checked⟩
    intro S h
    simp only [c9r5045targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 0 _ (by rfl)
  have c9r5046_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)] := by
    let c9r5046targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)]]
    let c9r5046choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5046targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)] c9r5046choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5046targets, c9r5046choice, ?_, checked⟩
    intro S h
    simp only [c9r5046targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 3 _ (by rfl)
  have c9r5047_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)] := by
    let c9r5047targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)]]
    let c9r5047choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r5047targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)] c9r5047choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5047targets, c9r5047choice, ?_, checked⟩
    intro S h
    simp only [c9r5047targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5040_closed
  · subst row; exact c9r5041_closed
  · subst row; exact c9r5042_closed
  · subst row; exact c9r5043_closed
  · subst row; exact c9r5044_closed
  · subst row; exact c9r5045_closed
  · subst row; exact c9r5046_closed
  · subst row; exact c9r5047_closed
theorem C9R05024G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5048_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)] := by
    let c9r5048targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,5)]]
    let c9r5048choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5048targets [(0,1),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)] c9r5048choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5048targets, c9r5048choice, ?_, checked⟩
    intro S h
    simp only [c9r5048targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 14 _ (by rfl)
  have c9r5049_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r5049targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r5049choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5049targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r5049choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5049targets, c9r5049choice, ?_, checked⟩
    intro S h
    simp only [c9r5049targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 20 _ (by rfl)
  have c9r5050_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r5050targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r5050choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5050targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c9r5050choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5050targets, c9r5050choice, ?_, checked⟩
    intro S h
    simp only [c9r5050targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 23 _ (by rfl)
  have c9r5051_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r5051targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r5051choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))))))
    have checked : successorFastRowCheck c9r5051targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] c9r5051choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5051targets, c9r5051choice, ?_, checked⟩
    intro S h
    simp only [c9r5051targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 25 _ (by rfl)
  have c9r5052_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r5052targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r5052choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5052targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] c9r5052choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5052targets, c9r5052choice, ?_, checked⟩
    intro S h
    simp only [c9r5052targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 27 _ (by rfl)
  have c9r5053_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] := by
    let c9r5053targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)]]
    let c9r5053choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5053targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] c9r5053choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5053targets, c9r5053choice, ?_, checked⟩
    intro S h
    simp only [c9r5053targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,true,false] 0 _ (by rfl)
  have c9r5054_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] := by
    let c9r5054targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)]]
    let c9r5054choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5054targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] c9r5054choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5054targets, c9r5054choice, ?_, checked⟩
    intro S h
    simp only [c9r5054targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,true,false] 3 _ (by rfl)
  have c9r5055_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] := by
    let c9r5055targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)]]
    let c9r5055choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5055targets [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] c9r5055choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5055targets, c9r5055choice, ?_, checked⟩
    intro S h
    simp only [c9r5055targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,true,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5048_closed
  · subst row; exact c9r5049_closed
  · subst row; exact c9r5050_closed
  · subst row; exact c9r5051_closed
  · subst row; exact c9r5052_closed
  · subst row; exact c9r5053_closed
  · subst row; exact c9r5054_closed
  · subst row; exact c9r5055_closed
theorem C9R05024_closed (row : List GridPoint) (h : FamilyMember row F9B002L29) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L29, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R05024G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05024G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05024G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05024G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05024G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05024G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05024G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05024G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05024G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05024G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05024G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05024G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05024G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05024G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05024G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05024G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05024G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05024G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05024G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05024G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05024G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05024G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05024G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05024G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05024G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05024G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05024G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05024G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05024G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05024G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05024G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05024G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
