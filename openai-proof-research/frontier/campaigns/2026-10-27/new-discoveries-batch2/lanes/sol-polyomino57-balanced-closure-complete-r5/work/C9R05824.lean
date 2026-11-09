import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R05824G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5824_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r5824targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r5824choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5824targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)] c9r5824choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5824targets, c9r5824choice, ?_, checked⟩
    intro S h
    simp only [c9r5824targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
  have c9r5825_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r5825targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r5825choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5825targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)] c9r5825choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5825targets, c9r5825choice, ?_, checked⟩
    intro S h
    simp only [c9r5825targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 19 _ (by rfl)
  have c9r5826_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r5826targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r5826choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5826targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)] c9r5826choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5826targets, c9r5826choice, ?_, checked⟩
    intro S h
    simp only [c9r5826targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 22 _ (by rfl)
  have c9r5827_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r5827targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r5827choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5827targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)] c9r5827choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5827targets, c9r5827choice, ?_, checked⟩
    intro S h
    simp only [c9r5827targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 25 _ (by rfl)
  have c9r5828_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r5828targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r5828choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5828targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)] c9r5828choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5828targets, c9r5828choice, ?_, checked⟩
    intro S h
    simp only [c9r5828targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 30 _ (by rfl)
  have c9r5829_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r5829targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r5829choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5829targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r5829choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5829targets, c9r5829choice, ?_, checked⟩
    intro S h
    simp only [c9r5829targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 0 _ (by rfl)
  have c9r5830_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r5830targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r5830choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5830targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r5830choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5830targets, c9r5830choice, ?_, checked⟩
    intro S h
    simp only [c9r5830targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 2 _ (by rfl)
  have c9r5831_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r5831targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r5831choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5831targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)] c9r5831choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5831targets, c9r5831choice, ?_, checked⟩
    intro S h
    simp only [c9r5831targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5824_closed
  · subst row; exact c9r5825_closed
  · subst row; exact c9r5826_closed
  · subst row; exact c9r5827_closed
  · subst row; exact c9r5828_closed
  · subst row; exact c9r5829_closed
  · subst row; exact c9r5830_closed
  · subst row; exact c9r5831_closed
theorem C9R05824G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5832_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r5832targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r5832choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5832targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)] c9r5832choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5832targets, c9r5832choice, ?_, checked⟩
    intro S h
    simp only [c9r5832targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 9 _ (by rfl)
  have c9r5833_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r5833targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r5833choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5833targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)] c9r5833choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5833targets, c9r5833choice, ?_, checked⟩
    intro S h
    simp only [c9r5833targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 11 _ (by rfl)
  have c9r5834_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r5834targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r5834choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5834targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)] c9r5834choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5834targets, c9r5834choice, ?_, checked⟩
    intro S h
    simp only [c9r5834targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 14 _ (by rfl)
  have c9r5835_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r5835targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r5835choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5835targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)] c9r5835choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5835targets, c9r5835choice, ?_, checked⟩
    intro S h
    simp only [c9r5835targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 17 _ (by rfl)
  have c9r5836_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r5836targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r5836choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5836targets [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] c9r5836choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5836targets, c9r5836choice, ?_, checked⟩
    intro S h
    simp only [c9r5836targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 20 _ (by rfl)
  have c9r5837_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r5837targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r5837choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5837targets [(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r5837choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5837targets, c9r5837choice, ?_, checked⟩
    intro S h
    simp only [c9r5837targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
  have c9r5838_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r5838targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5838choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5838targets [(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r5838choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5838targets, c9r5838choice, ?_, checked⟩
    intro S h
    simp only [c9r5838targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 30 _ (by rfl)
  have c9r5839_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r5839targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r5839choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5839targets [(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r5839choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5839targets, c9r5839choice, ?_, checked⟩
    intro S h
    simp only [c9r5839targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5832_closed
  · subst row; exact c9r5833_closed
  · subst row; exact c9r5834_closed
  · subst row; exact c9r5835_closed
  · subst row; exact c9r5836_closed
  · subst row; exact c9r5837_closed
  · subst row; exact c9r5838_closed
  · subst row; exact c9r5839_closed
theorem C9R05824G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5840_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r5840targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r5840choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5840targets [(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r5840choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5840targets, c9r5840choice, ?_, checked⟩
    intro S h
    simp only [c9r5840targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 3 _ (by rfl)
  have c9r5841_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r5841targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r5841choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5841targets [(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r5841choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5841targets, c9r5841choice, ?_, checked⟩
    intro S h
    simp only [c9r5841targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 5 _ (by rfl)
  have c9r5842_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] := by
    let c9r5842targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)]]
    let c9r5842choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5842targets [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] c9r5842choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5842targets, c9r5842choice, ?_, checked⟩
    intro S h
    simp only [c9r5842targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 12 _ (by rfl)
  have c9r5843_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r5843targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r5843choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5843targets [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r5843choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5843targets, c9r5843choice, ?_, checked⟩
    intro S h
    simp only [c9r5843targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 17 _ (by rfl)
  have c9r5844_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] := by
    let c9r5844targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)]]
    let c9r5844choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5844targets [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] c9r5844choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5844targets, c9r5844choice, ?_, checked⟩
    intro S h
    simp only [c9r5844targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 21 _ (by rfl)
  have c9r5845_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] := by
    let c9r5845targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)]]
    let c9r5845choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5845targets [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] c9r5845choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5845targets, c9r5845choice, ?_, checked⟩
    intro S h
    simp only [c9r5845targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 23 _ (by rfl)
  have c9r5846_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] := by
    let c9r5846targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)]]
    let c9r5846choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5846targets [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] c9r5846choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5846targets, c9r5846choice, ?_, checked⟩
    intro S h
    simp only [c9r5846targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 25 _ (by rfl)
  have c9r5847_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] := by
    let c9r5847targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)]]
    let c9r5847choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5847targets [(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] c9r5847choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5847targets, c9r5847choice, ?_, checked⟩
    intro S h
    simp only [c9r5847targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5840_closed
  · subst row; exact c9r5841_closed
  · subst row; exact c9r5842_closed
  · subst row; exact c9r5843_closed
  · subst row; exact c9r5844_closed
  · subst row; exact c9r5845_closed
  · subst row; exact c9r5846_closed
  · subst row; exact c9r5847_closed
theorem C9R05824G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5848_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r5848targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5848choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5848targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r5848choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5848targets, c9r5848choice, ?_, checked⟩
    intro S h
    simp only [c9r5848targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 5 _ (by rfl)
  have c9r5849_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r5849targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r5849choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5849targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r5849choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5849targets, c9r5849choice, ?_, checked⟩
    intro S h
    simp only [c9r5849targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 8 _ (by rfl)
  have c9r5850_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r5850targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r5850choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5850targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r5850choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5850targets, c9r5850choice, ?_, checked⟩
    intro S h
    simp only [c9r5850targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 10 _ (by rfl)
  have c9r5851_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r5851targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r5851choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5851targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r5851choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5851targets, c9r5851choice, ?_, checked⟩
    intro S h
    simp only [c9r5851targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 12 _ (by rfl)
  have c9r5852_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r5852targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r5852choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5852targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] c9r5852choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5852targets, c9r5852choice, ?_, checked⟩
    intro S h
    simp only [c9r5852targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 15 _ (by rfl)
  have c9r5853_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r5853targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r5853choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5853targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] c9r5853choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5853targets, c9r5853choice, ?_, checked⟩
    intro S h
    simp only [c9r5853targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 17 _ (by rfl)
  have c9r5854_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r5854targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r5854choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5854targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] c9r5854choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5854targets, c9r5854choice, ?_, checked⟩
    intro S h
    simp only [c9r5854targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 20 _ (by rfl)
  have c9r5855_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r5855targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r5855choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5855targets [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] c9r5855choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5855targets, c9r5855choice, ?_, checked⟩
    intro S h
    simp only [c9r5855targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5848_closed
  · subst row; exact c9r5849_closed
  · subst row; exact c9r5850_closed
  · subst row; exact c9r5851_closed
  · subst row; exact c9r5852_closed
  · subst row; exact c9r5853_closed
  · subst row; exact c9r5854_closed
  · subst row; exact c9r5855_closed
theorem C9R05824_closed (row : List GridPoint) (h : FamilyMember row F9B002L54) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L54, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R05824G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05824G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05824G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05824G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05824G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05824G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05824G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05824G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05824G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05824G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05824G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05824G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05824G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05824G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05824G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05824G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05824G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05824G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05824G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05824G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05824G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05824G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05824G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05824G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05824G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05824G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05824G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05824G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05824G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05824G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05824G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05824G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
