import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R05952G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5952_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] := by
    let c9r5952targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,2),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,2),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)]]
    let c9r5952choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5952targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] c9r5952choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5952targets, c9r5952choice, ?_, checked⟩
    intro S h
    simp only [c9r5952targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 2 _ (by rfl)
  have c9r5953_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)] := by
    let c9r5953targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c9r5953choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5953targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)] c9r5953choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5953targets, c9r5953choice, ?_, checked⟩
    intro S h
    simp only [c9r5953targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 5 _ (by rfl)
  have c9r5954_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)] := by
    let c9r5954targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)]]
    let c9r5954choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5954targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)] c9r5954choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5954targets, c9r5954choice, ?_, checked⟩
    intro S h
    simp only [c9r5954targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 8 _ (by rfl)
  have c9r5955_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)] := by
    let c9r5955targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)]]
    let c9r5955choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5955targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)] c9r5955choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5955targets, c9r5955choice, ?_, checked⟩
    intro S h
    simp only [c9r5955targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 11 _ (by rfl)
  have c9r5956_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)] := by
    let c9r5956targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c9r5956choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5956targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)] c9r5956choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5956targets, c9r5956choice, ?_, checked⟩
    intro S h
    simp only [c9r5956targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 14 _ (by rfl)
  have c9r5957_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)] := by
    let c9r5957targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c9r5957choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5957targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)] c9r5957choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5957targets, c9r5957choice, ?_, checked⟩
    intro S h
    simp only [c9r5957targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 17 _ (by rfl)
  have c9r5958_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)] := by
    let c9r5958targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c9r5958choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5958targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)] c9r5958choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5958targets, c9r5958choice, ?_, checked⟩
    intro S h
    simp only [c9r5958targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 20 _ (by rfl)
  have c9r5959_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)] := by
    let c9r5959targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c9r5959choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5959targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)] c9r5959choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5959targets, c9r5959choice, ?_, checked⟩
    intro S h
    simp only [c9r5959targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5952_closed
  · subst row; exact c9r5953_closed
  · subst row; exact c9r5954_closed
  · subst row; exact c9r5955_closed
  · subst row; exact c9r5956_closed
  · subst row; exact c9r5957_closed
  · subst row; exact c9r5958_closed
  · subst row; exact c9r5959_closed
theorem C9R05952G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5960_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r5960targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5960choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5960targets [(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)] c9r5960choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5960targets, c9r5960choice, ?_, checked⟩
    intro S h
    simp only [c9r5960targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 29 _ (by rfl)
  have c9r5961_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] := by
    let c9r5961targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)]]
    let c9r5961choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5961targets [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] c9r5961choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5961targets, c9r5961choice, ?_, checked⟩
    intro S h
    simp only [c9r5961targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 3 _ (by rfl)
  have c9r5962_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r5962targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r5962choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5962targets [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r5962choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5962targets, c9r5962choice, ?_, checked⟩
    intro S h
    simp only [c9r5962targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 8 _ (by rfl)
  have c9r5963_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] := by
    let c9r5963targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)]]
    let c9r5963choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5963targets [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] c9r5963choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5963targets, c9r5963choice, ?_, checked⟩
    intro S h
    simp only [c9r5963targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 12 _ (by rfl)
  have c9r5964_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] := by
    let c9r5964targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)]]
    let c9r5964choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5964targets [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] c9r5964choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5964targets, c9r5964choice, ?_, checked⟩
    intro S h
    simp only [c9r5964targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 14 _ (by rfl)
  have c9r5965_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] := by
    let c9r5965targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)]]
    let c9r5965choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5965targets [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] c9r5965choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5965targets, c9r5965choice, ?_, checked⟩
    intro S h
    simp only [c9r5965targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 16 _ (by rfl)
  have c9r5966_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] := by
    let c9r5966targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)]]
    let c9r5966choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5966targets [(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] c9r5966choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5966targets, c9r5966choice, ?_, checked⟩
    intro S h
    simp only [c9r5966targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 21 _ (by rfl)
  have c9r5967_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r5967targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5967choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5967targets [(0,1),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r5967choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5967targets, c9r5967choice, ?_, checked⟩
    intro S h
    simp only [c9r5967targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5960_closed
  · subst row; exact c9r5961_closed
  · subst row; exact c9r5962_closed
  · subst row; exact c9r5963_closed
  · subst row; exact c9r5964_closed
  · subst row; exact c9r5965_closed
  · subst row; exact c9r5966_closed
  · subst row; exact c9r5967_closed
theorem C9R05952G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5968_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r5968targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,5),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r5968choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5968targets [(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r5968choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5968targets, c9r5968choice, ?_, checked⟩
    intro S h
    simp only [c9r5968targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 5 _ (by rfl)
  have c9r5969_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r5969targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r5969choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5969targets [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r5969choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5969targets, c9r5969choice, ?_, checked⟩
    intro S h
    simp only [c9r5969targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 13 _ (by rfl)
  have c9r5970_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] := by
    let c9r5970targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,2),(1,2),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c9r5970choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5970targets [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] c9r5970choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5970targets, c9r5970choice, ?_, checked⟩
    intro S h
    simp only [c9r5970targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 18 _ (by rfl)
  have c9r5971_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r5971targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r5971choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5971targets [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r5971choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5971targets, c9r5971choice, ?_, checked⟩
    intro S h
    simp only [c9r5971targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 22 _ (by rfl)
  have c9r5972_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r5972targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r5972choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5972targets [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r5972choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5972targets, c9r5972choice, ?_, checked⟩
    intro S h
    simp only [c9r5972targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 25 _ (by rfl)
  have c9r5973_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r5973targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r5973choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5973targets [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r5973choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5973targets, c9r5973choice, ?_, checked⟩
    intro S h
    simp only [c9r5973targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 27 _ (by rfl)
  have c9r5974_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r5974targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r5974choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5974targets [(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r5974choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5974targets, c9r5974choice, ?_, checked⟩
    intro S h
    simp only [c9r5974targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 29 _ (by rfl)
  have c9r5975_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] := by
    let c9r5975targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,2),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)]]
    let c9r5975choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5975targets [(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] c9r5975choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5975targets, c9r5975choice, ?_, checked⟩
    intro S h
    simp only [c9r5975targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5968_closed
  · subst row; exact c9r5969_closed
  · subst row; exact c9r5970_closed
  · subst row; exact c9r5971_closed
  · subst row; exact c9r5972_closed
  · subst row; exact c9r5973_closed
  · subst row; exact c9r5974_closed
  · subst row; exact c9r5975_closed
theorem C9R05952G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5976_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r5976targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,5),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,2),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r5976choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r5976targets [(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r5976choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5976targets, c9r5976choice, ?_, checked⟩
    intro S h
    simp only [c9r5976targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 17 _ (by rfl)
  have c9r5977_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r5977targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r5977choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r5977targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] c9r5977choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5977targets, c9r5977choice, ?_, checked⟩
    intro S h
    simp only [c9r5977targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 27 _ (by rfl)
  have c9r5978_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)] := by
    let c9r5978targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(4,0)]]
    let c9r5978choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r5978targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)] c9r5978choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5978targets, c9r5978choice, ?_, checked⟩
    intro S h
    simp only [c9r5978targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 1 _ (by rfl)
  have c9r5979_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)] := by
    let c9r5979targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)]]
    let c9r5979choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5979targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)] c9r5979choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5979targets, c9r5979choice, ?_, checked⟩
    intro S h
    simp only [c9r5979targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 6 _ (by rfl)
  have c9r5980_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)] := by
    let c9r5980targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)]]
    let c9r5980choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5980targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)] c9r5980choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5980targets, c9r5980choice, ?_, checked⟩
    intro S h
    simp only [c9r5980targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 10 _ (by rfl)
  have c9r5981_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)] := by
    let c9r5981targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c9r5981choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5981targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)] c9r5981choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5981targets, c9r5981choice, ?_, checked⟩
    intro S h
    simp only [c9r5981targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 13 _ (by rfl)
  have c9r5982_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)] := by
    let c9r5982targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c9r5982choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5982targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)] c9r5982choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5982targets, c9r5982choice, ?_, checked⟩
    intro S h
    simp only [c9r5982targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 15 _ (by rfl)
  have c9r5983_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r5983targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r5983choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r5983targets [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] c9r5983choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5983targets, c9r5983choice, ?_, checked⟩
    intro S h
    simp only [c9r5983targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5976_closed
  · subst row; exact c9r5977_closed
  · subst row; exact c9r5978_closed
  · subst row; exact c9r5979_closed
  · subst row; exact c9r5980_closed
  · subst row; exact c9r5981_closed
  · subst row; exact c9r5982_closed
  · subst row; exact c9r5983_closed
theorem C9R05952_closed (row : List GridPoint) (h : FamilyMember row F9B002L58) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L58, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R05952G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05952G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05952G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05952G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05952G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05952G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05952G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05952G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05952G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05952G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05952G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05952G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05952G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05952G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05952G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05952G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05952G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05952G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05952G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05952G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05952G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05952G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05952G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05952G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05952G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05952G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05952G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05952G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05952G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05952G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05952G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05952G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
