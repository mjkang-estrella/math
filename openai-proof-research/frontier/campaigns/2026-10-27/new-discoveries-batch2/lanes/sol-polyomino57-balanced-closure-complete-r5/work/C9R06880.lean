import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06880G0 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6880_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)] := by
    let c9r6880targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c9r6880choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6880targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)] c9r6880choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6880targets, c9r6880choice, ?_, checked⟩
    intro S h
    simp only [c9r6880targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 27 _ (by rfl)
  have c9r6881_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r6881targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6881choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6881targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)] c9r6881choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6881targets, c9r6881choice, ?_, checked⟩
    intro S h
    simp only [c9r6881targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 0 _ (by rfl)
  have c9r6882_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c9r6882targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c9r6882choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6882targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)] c9r6882choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6882targets, c9r6882choice, ?_, checked⟩
    intro S h
    simp only [c9r6882targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 2 _ (by rfl)
  have c9r6883_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c9r6883targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c9r6883choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6883targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)] c9r6883choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6883targets, c9r6883choice, ?_, checked⟩
    intro S h
    simp only [c9r6883targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 4 _ (by rfl)
  have c9r6884_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)] := by
    let c9r6884targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)]]
    let c9r6884choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6884targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)] c9r6884choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6884targets, c9r6884choice, ?_, checked⟩
    intro S h
    simp only [c9r6884targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 8 _ (by rfl)
  have c9r6885_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)] := by
    let c9r6885targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)]]
    let c9r6885choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6885targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)] c9r6885choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6885targets, c9r6885choice, ?_, checked⟩
    intro S h
    simp only [c9r6885targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 11 _ (by rfl)
  have c9r6886_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)] := by
    let c9r6886targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)]]
    let c9r6886choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6886targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)] c9r6886choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6886targets, c9r6886choice, ?_, checked⟩
    intro S h
    simp only [c9r6886targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 14 _ (by rfl)
  have c9r6887_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)] := by
    let c9r6887targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)]]
    let c9r6887choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6887targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)] c9r6887choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6887targets, c9r6887choice, ?_, checked⟩
    intro S h
    simp only [c9r6887targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6880_closed
  · subst row; exact c9r6881_closed
  · subst row; exact c9r6882_closed
  · subst row; exact c9r6883_closed
  · subst row; exact c9r6884_closed
  · subst row; exact c9r6885_closed
  · subst row; exact c9r6886_closed
  · subst row; exact c9r6887_closed
theorem C9R06880G1 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6888_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)] := by
    let c9r6888targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)]]
    let c9r6888choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6888targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)] c9r6888choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6888targets, c9r6888choice, ?_, checked⟩
    intro S h
    simp only [c9r6888targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 19 _ (by rfl)
  have c9r6889_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)] := by
    let c9r6889targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c9r6889choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6889targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)] c9r6889choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6889targets, c9r6889choice, ?_, checked⟩
    intro S h
    simp only [c9r6889targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 23 _ (by rfl)
  have c9r6890_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)] := by
    let c9r6890targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c9r6890choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6890targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)] c9r6890choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6890targets, c9r6890choice, ?_, checked⟩
    intro S h
    simp only [c9r6890targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 26 _ (by rfl)
  have c9r6891_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c9r6891targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c9r6891choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6891targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)] c9r6891choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6891targets, c9r6891choice, ?_, checked⟩
    intro S h
    simp only [c9r6891targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 28 _ (by rfl)
  have c9r6892_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c9r6892targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c9r6892choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6892targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)] c9r6892choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6892targets, c9r6892choice, ?_, checked⟩
    intro S h
    simp only [c9r6892targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 31 _ (by rfl)
  have c9r6893_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c9r6893targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c9r6893choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6893targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)] c9r6893choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6893targets, c9r6893choice, ?_, checked⟩
    intro S h
    simp only [c9r6893targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 2 _ (by rfl)
  have c9r6894_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c9r6894targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c9r6894choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6894targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)] c9r6894choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6894targets, c9r6894choice, ?_, checked⟩
    intro S h
    simp only [c9r6894targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 5 _ (by rfl)
  have c9r6895_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c9r6895targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6895choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6895targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)] c9r6895choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6895targets, c9r6895choice, ?_, checked⟩
    intro S h
    simp only [c9r6895targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6888_closed
  · subst row; exact c9r6889_closed
  · subst row; exact c9r6890_closed
  · subst row; exact c9r6891_closed
  · subst row; exact c9r6892_closed
  · subst row; exact c9r6893_closed
  · subst row; exact c9r6894_closed
  · subst row; exact c9r6895_closed
theorem C9R06880G2 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6896_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c9r6896targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c9r6896choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6896targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)] c9r6896choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6896targets, c9r6896choice, ?_, checked⟩
    intro S h
    simp only [c9r6896targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 12 _ (by rfl)
  have c9r6897_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c9r6897targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c9r6897choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6897targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)] c9r6897choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6897targets, c9r6897choice, ?_, checked⟩
    intro S h
    simp only [c9r6897targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 14 _ (by rfl)
  have c9r6898_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c9r6898targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c9r6898choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6898targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)] c9r6898choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6898targets, c9r6898choice, ?_, checked⟩
    intro S h
    simp only [c9r6898targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 18 _ (by rfl)
  have c9r6899_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c9r6899targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c9r6899choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6899targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)] c9r6899choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6899targets, c9r6899choice, ?_, checked⟩
    intro S h
    simp only [c9r6899targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 21 _ (by rfl)
  have c9r6900_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c9r6900targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c9r6900choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6900targets [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)] c9r6900choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6900targets, c9r6900choice, ?_, checked⟩
    intro S h
    simp only [c9r6900targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 24 _ (by rfl)
  have c9r6901_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r6901targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6901choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6901targets [(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r6901choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6901targets, c9r6901choice, ?_, checked⟩
    intro S h
    simp only [c9r6901targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 29 _ (by rfl)
  have c9r6902_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r6902targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r6902choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6902targets [(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r6902choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6902targets, c9r6902choice, ?_, checked⟩
    intro S h
    simp only [c9r6902targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 2 _ (by rfl)
  have c9r6903_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r6903targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r6903choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6903targets [(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r6903choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6903targets, c9r6903choice, ?_, checked⟩
    intro S h
    simp only [c9r6903targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6896_closed
  · subst row; exact c9r6897_closed
  · subst row; exact c9r6898_closed
  · subst row; exact c9r6899_closed
  · subst row; exact c9r6900_closed
  · subst row; exact c9r6901_closed
  · subst row; exact c9r6902_closed
  · subst row; exact c9r6903_closed
theorem C9R06880G3 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6904_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r6904targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r6904choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6904targets [(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r6904choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6904targets, c9r6904choice, ?_, checked⟩
    intro S h
    simp only [c9r6904targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 7 _ (by rfl)
  have c9r6905_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r6905targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r6905choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6905targets [(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r6905choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6905targets, c9r6905choice, ?_, checked⟩
    intro S h
    simp only [c9r6905targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 9 _ (by rfl)
  have c9r6906_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] := by
    let c9r6906targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)]]
    let c9r6906choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6906targets [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] c9r6906choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6906targets, c9r6906choice, ?_, checked⟩
    intro S h
    simp only [c9r6906targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 16 _ (by rfl)
  have c9r6907_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r6907targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6907choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6907targets [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r6907choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6907targets, c9r6907choice, ?_, checked⟩
    intro S h
    simp only [c9r6907targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 21 _ (by rfl)
  have c9r6908_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] := by
    let c9r6908targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)]]
    let c9r6908choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6908targets [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] c9r6908choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6908targets, c9r6908choice, ?_, checked⟩
    intro S h
    simp only [c9r6908targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 25 _ (by rfl)
  have c9r6909_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] := by
    let c9r6909targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)]]
    let c9r6909choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6909targets [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] c9r6909choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6909targets, c9r6909choice, ?_, checked⟩
    intro S h
    simp only [c9r6909targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 27 _ (by rfl)
  have c9r6910_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] := by
    let c9r6910targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)]]
    let c9r6910choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6910targets [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] c9r6910choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6910targets, c9r6910choice, ?_, checked⟩
    intro S h
    simp only [c9r6910targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 29 _ (by rfl)
  have c9r6911_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] := by
    let c9r6911targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)]]
    let c9r6911choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6911targets [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] c9r6911choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6911targets, c9r6911choice, ?_, checked⟩
    intro S h
    simp only [c9r6911targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6904_closed
  · subst row; exact c9r6905_closed
  · subst row; exact c9r6906_closed
  · subst row; exact c9r6907_closed
  · subst row; exact c9r6908_closed
  · subst row; exact c9r6909_closed
  · subst row; exact c9r6910_closed
  · subst row; exact c9r6911_closed
theorem C9R06880_closed (row : List GridPoint) (h : FamilyMember row F9B003L23) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L23, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06880G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06880G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06880G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06880G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06880G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06880G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06880G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06880G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06880G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06880G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06880G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06880G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06880G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06880G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06880G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06880G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06880G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06880G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06880G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06880G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06880G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06880G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06880G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06880G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06880G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06880G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06880G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06880G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06880G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06880G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06880G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06880G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
