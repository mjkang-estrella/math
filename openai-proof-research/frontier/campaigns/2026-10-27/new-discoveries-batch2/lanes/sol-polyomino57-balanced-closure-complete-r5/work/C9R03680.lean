import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03680G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3680_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r3680targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r3680choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3680targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r3680choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3680targets, c9r3680choice, ?_, checked⟩
    intro S h
    simp only [c9r3680targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
  have c9r3681_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r3681targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r3681choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3681targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r3681choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3681targets, c9r3681choice, ?_, checked⟩
    intro S h
    simp only [c9r3681targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
  have c9r3682_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r3682targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r3682choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3682targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r3682choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3682targets, c9r3682choice, ?_, checked⟩
    intro S h
    simp only [c9r3682targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 24 _ (by rfl)
  have c9r3683_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r3683targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r3683choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3683targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r3683choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3683targets, c9r3683choice, ?_, checked⟩
    intro S h
    simp only [c9r3683targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 26 _ (by rfl)
  have c9r3684_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r3684targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r3684choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3684targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r3684choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3684targets, c9r3684choice, ?_, checked⟩
    intro S h
    simp only [c9r3684targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 29 _ (by rfl)
  have c9r3685_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r3685targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r3685choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3685targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r3685choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3685targets, c9r3685choice, ?_, checked⟩
    intro S h
    simp only [c9r3685targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
  have c9r3686_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r3686targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r3686choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3686targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r3686choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3686targets, c9r3686choice, ?_, checked⟩
    intro S h
    simp only [c9r3686targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 2 _ (by rfl)
  have c9r3687_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r3687targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r3687choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3687targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r3687choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3687targets, c9r3687choice, ?_, checked⟩
    intro S h
    simp only [c9r3687targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3680_closed
  · subst row; exact c9r3681_closed
  · subst row; exact c9r3682_closed
  · subst row; exact c9r3683_closed
  · subst row; exact c9r3684_closed
  · subst row; exact c9r3685_closed
  · subst row; exact c9r3686_closed
  · subst row; exact c9r3687_closed
theorem C9R03680G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3688_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r3688targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r3688choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3688targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r3688choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3688targets, c9r3688choice, ?_, checked⟩
    intro S h
    simp only [c9r3688targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 8 _ (by rfl)
  have c9r3689_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r3689targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r3689choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3689targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r3689choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3689targets, c9r3689choice, ?_, checked⟩
    intro S h
    simp only [c9r3689targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 11 _ (by rfl)
  have c9r3690_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r3690targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r3690choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3690targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r3690choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3690targets, c9r3690choice, ?_, checked⟩
    intro S h
    simp only [c9r3690targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 14 _ (by rfl)
  have c9r3691_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r3691targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r3691choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3691targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)] c9r3691choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3691targets, c9r3691choice, ?_, checked⟩
    intro S h
    simp only [c9r3691targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 19 _ (by rfl)
  have c9r3692_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r3692targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,4),(2,5),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,4),(2,5),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,4),(2,5),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r3692choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3692targets [(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)] c9r3692choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3692targets, c9r3692choice, ?_, checked⟩
    intro S h
    simp only [c9r3692targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 25 _ (by rfl)
  have c9r3693_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r3693targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3693choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3693targets [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r3693choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3693targets, c9r3693choice, ?_, checked⟩
    intro S h
    simp only [c9r3693targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 31 _ (by rfl)
  have c9r3694_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r3694targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r3694choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3694targets [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r3694choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3694targets, c9r3694choice, ?_, checked⟩
    intro S h
    simp only [c9r3694targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 3 _ (by rfl)
  have c9r3695_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r3695targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r3695choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3695targets [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r3695choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3695targets, c9r3695choice, ?_, checked⟩
    intro S h
    simp only [c9r3695targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3688_closed
  · subst row; exact c9r3689_closed
  · subst row; exact c9r3690_closed
  · subst row; exact c9r3691_closed
  · subst row; exact c9r3692_closed
  · subst row; exact c9r3693_closed
  · subst row; exact c9r3694_closed
  · subst row; exact c9r3695_closed
theorem C9R03680G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3696_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r3696targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r3696choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3696targets [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r3696choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3696targets, c9r3696choice, ?_, checked⟩
    intro S h
    simp only [c9r3696targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 8 _ (by rfl)
  have c9r3697_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r3697targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r3697choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3697targets [(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r3697choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3697targets, c9r3697choice, ?_, checked⟩
    intro S h
    simp only [c9r3697targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 10 _ (by rfl)
  have c9r3698_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r3698targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,5),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,5),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,5),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3698choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3698targets [(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r3698choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3698targets, c9r3698choice, ?_, checked⟩
    intro S h
    simp only [c9r3698targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
  have c9r3699_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r3699targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r3699choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (11,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c9r3699targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] c9r3699choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3699targets, c9r3699choice, ?_, checked⟩
    intro S h
    simp only [c9r3699targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 28 _ (by rfl)
  have c9r3700_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)] := by
    let c9r3700targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(5,0)]]
    let c9r3700choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3700targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)] c9r3700choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3700targets, c9r3700choice, ?_, checked⟩
    intro S h
    simp only [c9r3700targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 1 _ (by rfl)
  have c9r3701_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)] := by
    let c9r3701targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)]]
    let c9r3701choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3701targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)] c9r3701choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3701targets, c9r3701choice, ?_, checked⟩
    intro S h
    simp only [c9r3701targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 5 _ (by rfl)
  have c9r3702_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r3702targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r3702choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3702targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)] c9r3702choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3702targets, c9r3702choice, ?_, checked⟩
    intro S h
    simp only [c9r3702targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 8 _ (by rfl)
  have c9r3703_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r3703targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r3703choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3703targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)] c9r3703choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3703targets, c9r3703choice, ?_, checked⟩
    intro S h
    simp only [c9r3703targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3696_closed
  · subst row; exact c9r3697_closed
  · subst row; exact c9r3698_closed
  · subst row; exact c9r3699_closed
  · subst row; exact c9r3700_closed
  · subst row; exact c9r3701_closed
  · subst row; exact c9r3702_closed
  · subst row; exact c9r3703_closed
theorem C9R03680G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3704_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r3704targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r3704choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3704targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)] c9r3704choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3704targets, c9r3704choice, ?_, checked⟩
    intro S h
    simp only [c9r3704targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
  have c9r3705_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r3705targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r3705choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3705targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r3705choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3705targets, c9r3705choice, ?_, checked⟩
    intro S h
    simp only [c9r3705targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
  have c9r3706_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)] := by
    let c9r3706targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,2)]]
    let c9r3706choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3706targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)] c9r3706choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3706targets, c9r3706choice, ?_, checked⟩
    intro S h
    simp only [c9r3706targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
  have c9r3707_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)] := by
    let c9r3707targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,3)]]
    let c9r3707choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3707targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)] c9r3707choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3707targets, c9r3707choice, ?_, checked⟩
    intro S h
    simp only [c9r3707targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 22 _ (by rfl)
  have c9r3708_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)] := by
    let c9r3708targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(6,0)]]
    let c9r3708choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3708targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)] c9r3708choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3708targets, c9r3708choice, ?_, checked⟩
    intro S h
    simp only [c9r3708targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 24 _ (by rfl)
  have c9r3709_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r3709targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r3709choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3709targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)] c9r3709choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3709targets, c9r3709choice, ?_, checked⟩
    intro S h
    simp only [c9r3709targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 27 _ (by rfl)
  have c9r3710_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)] := by
    let c9r3710targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)]]
    let c9r3710choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3710targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)] c9r3710choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3710targets, c9r3710choice, ?_, checked⟩
    intro S h
    simp only [c9r3710targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 30 _ (by rfl)
  have c9r3711_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)] := by
    let c9r3711targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)]]
    let c9r3711choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3711targets [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)] c9r3711choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3711targets, c9r3711choice, ?_, checked⟩
    intro S h
    simp only [c9r3711targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3704_closed
  · subst row; exact c9r3705_closed
  · subst row; exact c9r3706_closed
  · subst row; exact c9r3707_closed
  · subst row; exact c9r3708_closed
  · subst row; exact c9r3709_closed
  · subst row; exact c9r3710_closed
  · subst row; exact c9r3711_closed
theorem C9R03680_closed (row : List GridPoint) (h : FamilyMember row F9B001L51) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L51, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03680G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03680G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03680G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03680G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03680G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03680G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03680G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03680G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03680G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03680G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03680G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03680G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03680G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03680G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03680G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03680G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03680G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03680G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03680G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03680G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03680G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03680G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03680G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03680G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03680G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03680G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03680G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03680G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03680G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03680G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03680G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03680G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
