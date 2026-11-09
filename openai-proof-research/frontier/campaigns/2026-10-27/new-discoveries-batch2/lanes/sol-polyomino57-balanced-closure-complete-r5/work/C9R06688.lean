import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06688G0 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6688_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)] := by
    let c9r6688targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c9r6688choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6688targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)] c9r6688choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6688targets, c9r6688choice, ?_, checked⟩
    intro S h
    simp only [c9r6688targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 11 _ (by rfl)
  have c9r6689_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)] := by
    let c9r6689targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6689choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6689targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)] c9r6689choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6689targets, c9r6689choice, ?_, checked⟩
    intro S h
    simp only [c9r6689targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 16 _ (by rfl)
  have c9r6690_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)] := by
    let c9r6690targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c9r6690choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6690targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)] c9r6690choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6690targets, c9r6690choice, ?_, checked⟩
    intro S h
    simp only [c9r6690targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 18 _ (by rfl)
  have c9r6691_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)] := by
    let c9r6691targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c9r6691choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6691targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)] c9r6691choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6691targets, c9r6691choice, ?_, checked⟩
    intro S h
    simp only [c9r6691targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 20 _ (by rfl)
  have c9r6692_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)] := by
    let c9r6692targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c9r6692choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6692targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)] c9r6692choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6692targets, c9r6692choice, ?_, checked⟩
    intro S h
    simp only [c9r6692targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 24 _ (by rfl)
  have c9r6693_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)] := by
    let c9r6693targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c9r6693choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6693targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)] c9r6693choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6693targets, c9r6693choice, ?_, checked⟩
    intro S h
    simp only [c9r6693targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 27 _ (by rfl)
  have c9r6694_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)] := by
    let c9r6694targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c9r6694choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6694targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)] c9r6694choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6694targets, c9r6694choice, ?_, checked⟩
    intro S h
    simp only [c9r6694targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 29 _ (by rfl)
  have c9r6695_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)] := by
    let c9r6695targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c9r6695choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6695targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)] c9r6695choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6695targets, c9r6695choice, ?_, checked⟩
    intro S h
    simp only [c9r6695targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6688_closed
  · subst row; exact c9r6689_closed
  · subst row; exact c9r6690_closed
  · subst row; exact c9r6691_closed
  · subst row; exact c9r6692_closed
  · subst row; exact c9r6693_closed
  · subst row; exact c9r6694_closed
  · subst row; exact c9r6695_closed
theorem C9R06688G1 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6696_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)] := by
    let c9r6696targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c9r6696choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6696targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)] c9r6696choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6696targets, c9r6696choice, ?_, checked⟩
    intro S h
    simp only [c9r6696targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 3 _ (by rfl)
  have c9r6697_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)] := by
    let c9r6697targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c9r6697choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6697targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)] c9r6697choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6697targets, c9r6697choice, ?_, checked⟩
    intro S h
    simp only [c9r6697targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 6 _ (by rfl)
  have c9r6698_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r6698targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r6698choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6698targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)] c9r6698choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6698targets, c9r6698choice, ?_, checked⟩
    intro S h
    simp only [c9r6698targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 11 _ (by rfl)
  have c9r6699_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r6699targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r6699choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6699targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)] c9r6699choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6699targets, c9r6699choice, ?_, checked⟩
    intro S h
    simp only [c9r6699targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 15 _ (by rfl)
  have c9r6700_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r6700targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r6700choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6700targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)] c9r6700choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6700targets, c9r6700choice, ?_, checked⟩
    intro S h
    simp only [c9r6700targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 17 _ (by rfl)
  have c9r6701_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r6701targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r6701choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6701targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)] c9r6701choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6701targets, c9r6701choice, ?_, checked⟩
    intro S h
    simp only [c9r6701targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 19 _ (by rfl)
  have c9r6702_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)] := by
    let c9r6702targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c9r6702choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6702targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)] c9r6702choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6702targets, c9r6702choice, ?_, checked⟩
    intro S h
    simp only [c9r6702targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 23 _ (by rfl)
  have c9r6703_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)] := by
    let c9r6703targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c9r6703choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6703targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)] c9r6703choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6703targets, c9r6703choice, ?_, checked⟩
    intro S h
    simp only [c9r6703targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6696_closed
  · subst row; exact c9r6697_closed
  · subst row; exact c9r6698_closed
  · subst row; exact c9r6699_closed
  · subst row; exact c9r6700_closed
  · subst row; exact c9r6701_closed
  · subst row; exact c9r6702_closed
  · subst row; exact c9r6703_closed
theorem C9R06688G2 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6704_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)] := by
    let c9r6704targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c9r6704choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6704targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)] c9r6704choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6704targets, c9r6704choice, ?_, checked⟩
    intro S h
    simp only [c9r6704targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 29 _ (by rfl)
  have c9r6705_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)] := by
    let c9r6705targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c9r6705choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6705targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)] c9r6705choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6705targets, c9r6705choice, ?_, checked⟩
    intro S h
    simp only [c9r6705targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 0 _ (by rfl)
  have c9r6706_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)] := by
    let c9r6706targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c9r6706choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6706targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)] c9r6706choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6706targets, c9r6706choice, ?_, checked⟩
    intro S h
    simp only [c9r6706targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 3 _ (by rfl)
  have c9r6707_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r6707targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6707choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6707targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)] c9r6707choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6707targets, c9r6707choice, ?_, checked⟩
    intro S h
    simp only [c9r6707targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 8 _ (by rfl)
  have c9r6708_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)] := by
    let c9r6708targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c9r6708choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6708targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)] c9r6708choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6708targets, c9r6708choice, ?_, checked⟩
    intro S h
    simp only [c9r6708targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 12 _ (by rfl)
  have c9r6709_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)] := by
    let c9r6709targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c9r6709choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6709targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)] c9r6709choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6709targets, c9r6709choice, ?_, checked⟩
    intro S h
    simp only [c9r6709targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 15 _ (by rfl)
  have c9r6710_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)] := by
    let c9r6710targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c9r6710choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6710targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)] c9r6710choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6710targets, c9r6710choice, ?_, checked⟩
    intro S h
    simp only [c9r6710targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 17 _ (by rfl)
  have c9r6711_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)] := by
    let c9r6711targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6711choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6711targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)] c9r6711choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6711targets, c9r6711choice, ?_, checked⟩
    intro S h
    simp only [c9r6711targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6704_closed
  · subst row; exact c9r6705_closed
  · subst row; exact c9r6706_closed
  · subst row; exact c9r6707_closed
  · subst row; exact c9r6708_closed
  · subst row; exact c9r6709_closed
  · subst row; exact c9r6710_closed
  · subst row; exact c9r6711_closed
theorem C9R06688G3 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6712_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)] := by
    let c9r6712targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c9r6712choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6712targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)] c9r6712choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6712targets, c9r6712choice, ?_, checked⟩
    intro S h
    simp only [c9r6712targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 24 _ (by rfl)
  have c9r6713_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)] := by
    let c9r6713targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c9r6713choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6713targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)] c9r6713choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6713targets, c9r6713choice, ?_, checked⟩
    intro S h
    simp only [c9r6713targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 26 _ (by rfl)
  have c9r6714_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)] := by
    let c9r6714targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c9r6714choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6714targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)] c9r6714choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6714targets, c9r6714choice, ?_, checked⟩
    intro S h
    simp only [c9r6714targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 30 _ (by rfl)
  have c9r6715_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)] := by
    let c9r6715targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c9r6715choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6715targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)] c9r6715choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6715targets, c9r6715choice, ?_, checked⟩
    intro S h
    simp only [c9r6715targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 1 _ (by rfl)
  have c9r6716_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)] := by
    let c9r6716targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c9r6716choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6716targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)] c9r6716choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6716targets, c9r6716choice, ?_, checked⟩
    intro S h
    simp only [c9r6716targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 4 _ (by rfl)
  have c9r6717_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] := by
    let c9r6717targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)]]
    let c9r6717choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6717targets [(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] c9r6717choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6717targets, c9r6717choice, ?_, checked⟩
    intro S h
    simp only [c9r6717targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 10 _ (by rfl)
  have c9r6718_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r6718targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r6718choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6718targets [(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r6718choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6718targets, c9r6718choice, ?_, checked⟩
    intro S h
    simp only [c9r6718targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 15 _ (by rfl)
  have c9r6719_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r6719targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r6719choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6719targets [(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)] c9r6719choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6719targets, c9r6719choice, ?_, checked⟩
    intro S h
    simp only [c9r6719targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6712_closed
  · subst row; exact c9r6713_closed
  · subst row; exact c9r6714_closed
  · subst row; exact c9r6715_closed
  · subst row; exact c9r6716_closed
  · subst row; exact c9r6717_closed
  · subst row; exact c9r6718_closed
  · subst row; exact c9r6719_closed
theorem C9R06688_closed (row : List GridPoint) (h : FamilyMember row F9B003L17) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L17, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06688G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06688G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06688G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06688G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06688G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06688G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06688G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06688G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06688G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06688G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06688G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06688G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06688G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06688G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06688G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06688G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06688G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06688G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06688G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06688G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06688G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06688G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06688G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06688G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06688G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06688G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06688G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06688G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06688G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06688G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06688G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06688G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
