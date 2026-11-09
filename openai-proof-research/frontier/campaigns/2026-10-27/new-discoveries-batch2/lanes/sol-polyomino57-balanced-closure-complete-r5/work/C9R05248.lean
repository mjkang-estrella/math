import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R05248G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5248_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c9r5248targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c9r5248choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5248targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)] c9r5248choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5248targets, c9r5248choice, ?_, checked⟩
    intro S h
    simp only [c9r5248targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 19 _ (by rfl)
  have c9r5249_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c9r5249targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c9r5249choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5249targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)] c9r5249choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5249targets, c9r5249choice, ?_, checked⟩
    intro S h
    simp only [c9r5249targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 22 _ (by rfl)
  have c9r5250_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c9r5250targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c9r5250choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5250targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)] c9r5250choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5250targets, c9r5250choice, ?_, checked⟩
    intro S h
    simp only [c9r5250targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 26 _ (by rfl)
  have c9r5251_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c9r5251targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c9r5251choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5251targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)] c9r5251choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5251targets, c9r5251choice, ?_, checked⟩
    intro S h
    simp only [c9r5251targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 29 _ (by rfl)
  have c9r5252_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c9r5252targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c9r5252choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5252targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)] c9r5252choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5252targets, c9r5252choice, ?_, checked⟩
    intro S h
    simp only [c9r5252targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 31 _ (by rfl)
  have c9r5253_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c9r5253targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c9r5253choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5253targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)] c9r5253choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5253targets, c9r5253choice, ?_, checked⟩
    intro S h
    simp only [c9r5253targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 3 _ (by rfl)
  have c9r5254_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c9r5254targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c9r5254choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5254targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)] c9r5254choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5254targets, c9r5254choice, ?_, checked⟩
    intro S h
    simp only [c9r5254targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 6 _ (by rfl)
  have c9r5255_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c9r5255targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c9r5255choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5255targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)] c9r5255choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5255targets, c9r5255choice, ?_, checked⟩
    intro S h
    simp only [c9r5255targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5248_closed
  · subst row; exact c9r5249_closed
  · subst row; exact c9r5250_closed
  · subst row; exact c9r5251_closed
  · subst row; exact c9r5252_closed
  · subst row; exact c9r5253_closed
  · subst row; exact c9r5254_closed
  · subst row; exact c9r5255_closed
theorem C9R05248G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5256_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r5256targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5256choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5256targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)] c9r5256choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5256targets, c9r5256choice, ?_, checked⟩
    intro S h
    simp only [c9r5256targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 15 _ (by rfl)
  have c9r5257_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r5257targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5257choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5257targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)] c9r5257choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5257targets, c9r5257choice, ?_, checked⟩
    intro S h
    simp only [c9r5257targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 21 _ (by rfl)
  have c9r5258_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r5258targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r5258choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5258targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)] c9r5258choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5258targets, c9r5258choice, ?_, checked⟩
    intro S h
    simp only [c9r5258targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 24 _ (by rfl)
  have c9r5259_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r5259targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r5259choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5259targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)] c9r5259choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5259targets, c9r5259choice, ?_, checked⟩
    intro S h
    simp only [c9r5259targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 26 _ (by rfl)
  have c9r5260_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r5260targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r5260choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5260targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)] c9r5260choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5260targets, c9r5260choice, ?_, checked⟩
    intro S h
    simp only [c9r5260targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 28 _ (by rfl)
  have c9r5261_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r5261targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r5261choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5261targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)] c9r5261choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5261targets, c9r5261choice, ?_, checked⟩
    intro S h
    simp only [c9r5261targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 31 _ (by rfl)
  have c9r5262_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r5262targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r5262choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5262targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)] c9r5262choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5262targets, c9r5262choice, ?_, checked⟩
    intro S h
    simp only [c9r5262targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 1 _ (by rfl)
  have c9r5263_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r5263targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r5263choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5263targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)] c9r5263choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5263targets, c9r5263choice, ?_, checked⟩
    intro S h
    simp only [c9r5263targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5256_closed
  · subst row; exact c9r5257_closed
  · subst row; exact c9r5258_closed
  · subst row; exact c9r5259_closed
  · subst row; exact c9r5260_closed
  · subst row; exact c9r5261_closed
  · subst row; exact c9r5262_closed
  · subst row; exact c9r5263_closed
theorem C9R05248G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5264_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r5264targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r5264choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5264targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)] c9r5264choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5264targets, c9r5264choice, ?_, checked⟩
    intro S h
    simp only [c9r5264targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 7 _ (by rfl)
  have c9r5265_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r5265targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r5265choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5265targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)] c9r5265choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5265targets, c9r5265choice, ?_, checked⟩
    intro S h
    simp only [c9r5265targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 12 _ (by rfl)
  have c9r5266_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r5266targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r5266choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5266targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)] c9r5266choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5266targets, c9r5266choice, ?_, checked⟩
    intro S h
    simp only [c9r5266targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 16 _ (by rfl)
  have c9r5267_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r5267targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r5267choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5267targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)] c9r5267choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5267targets, c9r5267choice, ?_, checked⟩
    intro S h
    simp only [c9r5267targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 18 _ (by rfl)
  have c9r5268_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r5268targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r5268choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5268targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)] c9r5268choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5268targets, c9r5268choice, ?_, checked⟩
    intro S h
    simp only [c9r5268targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 20 _ (by rfl)
  have c9r5269_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r5269targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r5269choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5269targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)] c9r5269choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5269targets, c9r5269choice, ?_, checked⟩
    intro S h
    simp only [c9r5269targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 23 _ (by rfl)
  have c9r5270_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r5270targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r5270choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5270targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)] c9r5270choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5270targets, c9r5270choice, ?_, checked⟩
    intro S h
    simp only [c9r5270targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 26 _ (by rfl)
  have c9r5271_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r5271targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r5271choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5271targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)] c9r5271choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5271targets, c9r5271choice, ?_, checked⟩
    intro S h
    simp only [c9r5271targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5264_closed
  · subst row; exact c9r5265_closed
  · subst row; exact c9r5266_closed
  · subst row; exact c9r5267_closed
  · subst row; exact c9r5268_closed
  · subst row; exact c9r5269_closed
  · subst row; exact c9r5270_closed
  · subst row; exact c9r5271_closed
theorem C9R05248G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5272_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r5272targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r5272choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5272targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)] c9r5272choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5272targets, c9r5272choice, ?_, checked⟩
    intro S h
    simp only [c9r5272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 0 _ (by rfl)
  have c9r5273_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r5273targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r5273choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5273targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)] c9r5273choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5273targets, c9r5273choice, ?_, checked⟩
    intro S h
    simp only [c9r5273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 3 _ (by rfl)
  have c9r5274_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r5274targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r5274choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5274targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)] c9r5274choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5274targets, c9r5274choice, ?_, checked⟩
    intro S h
    simp only [c9r5274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 8 _ (by rfl)
  have c9r5275_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r5275targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r5275choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5275targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r5275choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5275targets, c9r5275choice, ?_, checked⟩
    intro S h
    simp only [c9r5275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 10 _ (by rfl)
  have c9r5276_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r5276targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r5276choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5276targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r5276choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5276targets, c9r5276choice, ?_, checked⟩
    intro S h
    simp only [c9r5276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 12 _ (by rfl)
  have c9r5277_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r5277targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r5277choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5277targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)] c9r5277choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5277targets, c9r5277choice, ?_, checked⟩
    intro S h
    simp only [c9r5277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 16 _ (by rfl)
  have c9r5278_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r5278targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r5278choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5278targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)] c9r5278choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5278targets, c9r5278choice, ?_, checked⟩
    intro S h
    simp only [c9r5278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 19 _ (by rfl)
  have c9r5279_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r5279targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r5279choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5279targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)] c9r5279choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5279targets, c9r5279choice, ?_, checked⟩
    intro S h
    simp only [c9r5279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5272_closed
  · subst row; exact c9r5273_closed
  · subst row; exact c9r5274_closed
  · subst row; exact c9r5275_closed
  · subst row; exact c9r5276_closed
  · subst row; exact c9r5277_closed
  · subst row; exact c9r5278_closed
  · subst row; exact c9r5279_closed
theorem C9R05248_closed (row : List GridPoint) (h : FamilyMember row F9B002L36) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L36, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R05248G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05248G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05248G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05248G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05248G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05248G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05248G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05248G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05248G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05248G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05248G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05248G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05248G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05248G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05248G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05248G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05248G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05248G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05248G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05248G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05248G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05248G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05248G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05248G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05248G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05248G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05248G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05248G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05248G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05248G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05248G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05248G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
