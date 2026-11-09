import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06368G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6368_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)] := by
    let c9r6368targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)]]
    let c9r6368choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6368targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)] c9r6368choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6368targets, c9r6368choice, ?_, checked⟩
    intro S h
    simp only [c9r6368targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 29 _ (by rfl)
  have c9r6369_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)] := by
    let c9r6369targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2),(6,2)]]
    let c9r6369choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6369targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)] c9r6369choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6369targets, c9r6369choice, ?_, checked⟩
    intro S h
    simp only [c9r6369targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 31 _ (by rfl)
  have c9r6370_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)] := by
    let c9r6370targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3),(6,3)]]
    let c9r6370choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6370targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)] c9r6370choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6370targets, c9r6370choice, ?_, checked⟩
    intro S h
    simp only [c9r6370targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 1 _ (by rfl)
  have c9r6371_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r6371targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r6371choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6371targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)] c9r6371choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6371targets, c9r6371choice, ?_, checked⟩
    intro S h
    simp only [c9r6371targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 4 _ (by rfl)
  have c9r6372_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)] := by
    let c9r6372targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(6,2)]]
    let c9r6372choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6372targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)] c9r6372choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6372targets, c9r6372choice, ?_, checked⟩
    intro S h
    simp only [c9r6372targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 7 _ (by rfl)
  have c9r6373_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)] := by
    let c9r6373targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0),(7,0)]]
    let c9r6373choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6373targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)] c9r6373choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6373targets, c9r6373choice, ?_, checked⟩
    intro S h
    simp only [c9r6373targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 9 _ (by rfl)
  have c9r6374_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)] := by
    let c9r6374targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(6,2)]]
    let c9r6374choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6374targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)] c9r6374choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6374targets, c9r6374choice, ?_, checked⟩
    intro S h
    simp only [c9r6374targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 12 _ (by rfl)
  have c9r6375_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)] := by
    let c9r6375targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1),(7,1)]]
    let c9r6375choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6375targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)] c9r6375choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6375targets, c9r6375choice, ?_, checked⟩
    intro S h
    simp only [c9r6375targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6368_closed
  · subst row; exact c9r6369_closed
  · subst row; exact c9r6370_closed
  · subst row; exact c9r6371_closed
  · subst row; exact c9r6372_closed
  · subst row; exact c9r6373_closed
  · subst row; exact c9r6374_closed
  · subst row; exact c9r6375_closed
theorem C9R06368G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6376_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)] := by
    let c9r6376targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3),(6,3)]]
    let c9r6376choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6376targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)] c9r6376choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6376targets, c9r6376choice, ?_, checked⟩
    intro S h
    simp only [c9r6376targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 18 _ (by rfl)
  have c9r6377_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)] := by
    let c9r6377targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3),(6,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2),(7,2)]]
    let c9r6377choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6377targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)] c9r6377choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6377targets, c9r6377choice, ?_, checked⟩
    intro S h
    simp only [c9r6377targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 21 _ (by rfl)
  have c9r6378_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)] := by
    let c9r6378targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c9r6378choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6378targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)] c9r6378choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6378targets, c9r6378choice, ?_, checked⟩
    intro S h
    simp only [c9r6378targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 26 _ (by rfl)
  have c9r6379_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)] := by
    let c9r6379targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c9r6379choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6379targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)] c9r6379choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6379targets, c9r6379choice, ?_, checked⟩
    intro S h
    simp only [c9r6379targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 28 _ (by rfl)
  have c9r6380_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)] := by
    let c9r6380targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c9r6380choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6380targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)] c9r6380choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6380targets, c9r6380choice, ?_, checked⟩
    intro S h
    simp only [c9r6380targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 30 _ (by rfl)
  have c9r6381_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)] := by
    let c9r6381targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1),(7,1)]]
    let c9r6381choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6381targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)] c9r6381choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6381targets, c9r6381choice, ?_, checked⟩
    intro S h
    simp only [c9r6381targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 1 _ (by rfl)
  have c9r6382_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)] := by
    let c9r6382targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0),(8,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1),(7,0),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0),(8,0)]]
    let c9r6382choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < -1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r6382targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)] c9r6382choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6382targets, c9r6382choice, ?_, checked⟩
    intro S h
    simp only [c9r6382targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 3 _ (by rfl)
  have c9r6383_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)] := by
    let c9r6383targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,3),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3),(6,3)]]
    let c9r6383choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6383targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)] c9r6383choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6383targets, c9r6383choice, ?_, checked⟩
    intro S h
    simp only [c9r6383targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6376_closed
  · subst row; exact c9r6377_closed
  · subst row; exact c9r6378_closed
  · subst row; exact c9r6379_closed
  · subst row; exact c9r6380_closed
  · subst row; exact c9r6381_closed
  · subst row; exact c9r6382_closed
  · subst row; exact c9r6383_closed
theorem C9R06368G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6384_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)] := by
    let c9r6384targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1),(7,1)]]
    let c9r6384choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6384targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)] c9r6384choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6384targets, c9r6384choice, ?_, checked⟩
    intro S h
    simp only [c9r6384targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 10 _ (by rfl)
  have c9r6385_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)] := by
    let c9r6385targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(6,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2),(7,2)]]
    let c9r6385choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6385targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)] c9r6385choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6385targets, c9r6385choice, ?_, checked⟩
    intro S h
    simp only [c9r6385targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 12 _ (by rfl)
  have c9r6386_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)] := by
    let c9r6386targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1),(7,1)]]
    let c9r6386choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6386targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)] c9r6386choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6386targets, c9r6386choice, ?_, checked⟩
    intro S h
    simp only [c9r6386targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 15 _ (by rfl)
  have c9r6387_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)] := by
    let c9r6387targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2),(7,2)]]
    let c9r6387choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6387targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)] c9r6387choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6387targets, c9r6387choice, ?_, checked⟩
    intro S h
    simp only [c9r6387targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 18 _ (by rfl)
  have c9r6388_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)] := by
    let c9r6388targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1),(8,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2),(7,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1),(8,1)]]
    let c9r6388choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r6388targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)] c9r6388choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6388targets, c9r6388choice, ?_, checked⟩
    intro S h
    simp only [c9r6388targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 21 _ (by rfl)
  have c9r6389_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)] := by
    let c9r6389targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(6,1)]]
    let c9r6389choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6389targets [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)] c9r6389choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6389targets, c9r6389choice, ?_, checked⟩
    intro S h
    simp only [c9r6389targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 26 _ (by rfl)
  have c9r6390_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r6390targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r6390choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6390targets [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)] c9r6390choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6390targets, c9r6390choice, ?_, checked⟩
    intro S h
    simp only [c9r6390targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 31 _ (by rfl)
  have c9r6391_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)] := by
    let c9r6391targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0),(7,0)]]
    let c9r6391choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6391targets [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)] c9r6391choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6391targets, c9r6391choice, ?_, checked⟩
    intro S h
    simp only [c9r6391targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6384_closed
  · subst row; exact c9r6385_closed
  · subst row; exact c9r6386_closed
  · subst row; exact c9r6387_closed
  · subst row; exact c9r6388_closed
  · subst row; exact c9r6389_closed
  · subst row; exact c9r6390_closed
  · subst row; exact c9r6391_closed
theorem C9R06368G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6392_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)] := by
    let c9r6392targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1),(7,1)]]
    let c9r6392choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6392targets [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)] c9r6392choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6392targets, c9r6392choice, ?_, checked⟩
    intro S h
    simp only [c9r6392targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 3 _ (by rfl)
  have c9r6393_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)] := by
    let c9r6393targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1),(7,1)]]
    let c9r6393choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6393targets [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)] c9r6393choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6393targets, c9r6393choice, ?_, checked⟩
    intro S h
    simp only [c9r6393targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 7 _ (by rfl)
  have c9r6394_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)] := by
    let c9r6394targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,3)]]
    let c9r6394choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r6394targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)] c9r6394choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6394targets, c9r6394choice, ?_, checked⟩
    intro S h
    simp only [c9r6394targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 15 _ (by rfl)
  have c9r6395_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)] := by
    let c9r6395targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(7,0)]]
    let c9r6395choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6395targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)] c9r6395choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6395targets, c9r6395choice, ?_, checked⟩
    intro S h
    simp only [c9r6395targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 18 _ (by rfl)
  have c9r6396_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)] := by
    let c9r6396targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1),(7,1)]]
    let c9r6396choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6396targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)] c9r6396choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6396targets, c9r6396choice, ?_, checked⟩
    intro S h
    simp only [c9r6396targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 20 _ (by rfl)
  have c9r6397_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)] := by
    let c9r6397targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2),(6,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2),(7,2)]]
    let c9r6397choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6397targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)] c9r6397choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6397targets, c9r6397choice, ?_, checked⟩
    intro S h
    simp only [c9r6397targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 22 _ (by rfl)
  have c9r6398_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)] := by
    let c9r6398targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1),(7,1)]]
    let c9r6398choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6398targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)] c9r6398choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6398targets, c9r6398choice, ?_, checked⟩
    intro S h
    simp only [c9r6398targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 25 _ (by rfl)
  have c9r6399_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)] := by
    let c9r6399targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0),(8,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,1),(7,0),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0),(7,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0),(8,0)]]
    let c9r6399choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < -1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r6399targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)] c9r6399choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6399targets, c9r6399choice, ?_, checked⟩
    intro S h
    simp only [c9r6399targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6392_closed
  · subst row; exact c9r6393_closed
  · subst row; exact c9r6394_closed
  · subst row; exact c9r6395_closed
  · subst row; exact c9r6396_closed
  · subst row; exact c9r6397_closed
  · subst row; exact c9r6398_closed
  · subst row; exact c9r6399_closed
theorem C9R06368_closed (row : List GridPoint) (h : FamilyMember row F9B003L7) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L7, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06368G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06368G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06368G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06368G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06368G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06368G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06368G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06368G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06368G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06368G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06368G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06368G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06368G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06368G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06368G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06368G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06368G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06368G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06368G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06368G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06368G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06368G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06368G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06368G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06368G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06368G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06368G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06368G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06368G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06368G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06368G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06368G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
