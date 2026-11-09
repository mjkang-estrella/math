import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R07712G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7712_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r7712targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r7712choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7712targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r7712choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7712targets, c9r7712choice, ?_, checked⟩
    intro S h
    simp only [c9r7712targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 11 _ (by rfl)
  have c9r7713_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r7713targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r7713choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7713targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r7713choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7713targets, c9r7713choice, ?_, checked⟩
    intro S h
    simp only [c9r7713targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 13 _ (by rfl)
  have c9r7714_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r7714targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r7714choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7714targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r7714choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7714targets, c9r7714choice, ?_, checked⟩
    intro S h
    simp only [c9r7714targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 15 _ (by rfl)
  have c9r7715_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r7715targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r7715choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7715targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r7715choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7715targets, c9r7715choice, ?_, checked⟩
    intro S h
    simp only [c9r7715targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 18 _ (by rfl)
  have c9r7716_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r7716targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r7716choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7716targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r7716choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7716targets, c9r7716choice, ?_, checked⟩
    intro S h
    simp only [c9r7716targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 21 _ (by rfl)
  have c9r7717_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r7717targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r7717choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7717targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r7717choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7717targets, c9r7717choice, ?_, checked⟩
    intro S h
    simp only [c9r7717targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 23 _ (by rfl)
  have c9r7718_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r7718targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r7718choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7718targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r7718choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7718targets, c9r7718choice, ?_, checked⟩
    intro S h
    simp only [c9r7718targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 26 _ (by rfl)
  have c9r7719_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r7719targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r7719choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7719targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r7719choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7719targets, c9r7719choice, ?_, checked⟩
    intro S h
    simp only [c9r7719targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7712_closed
  · subst row; exact c9r7713_closed
  · subst row; exact c9r7714_closed
  · subst row; exact c9r7715_closed
  · subst row; exact c9r7716_closed
  · subst row; exact c9r7717_closed
  · subst row; exact c9r7718_closed
  · subst row; exact c9r7719_closed
theorem C9R07712G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7720_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r7720targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r7720choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7720targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r7720choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7720targets, c9r7720choice, ?_, checked⟩
    intro S h
    simp only [c9r7720targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 0 _ (by rfl)
  have c9r7721_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r7721targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r7721choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7721targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r7721choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7721targets, c9r7721choice, ?_, checked⟩
    intro S h
    simp only [c9r7721targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 3 _ (by rfl)
  have c9r7722_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r7722targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r7722choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7722targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)] c9r7722choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7722targets, c9r7722choice, ?_, checked⟩
    intro S h
    simp only [c9r7722targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 8 _ (by rfl)
  have c9r7723_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r7723targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r7723choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7723targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)] c9r7723choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7723targets, c9r7723choice, ?_, checked⟩
    intro S h
    simp only [c9r7723targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 10 _ (by rfl)
  have c9r7724_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r7724targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r7724choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7724targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)] c9r7724choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7724targets, c9r7724choice, ?_, checked⟩
    intro S h
    simp only [c9r7724targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 12 _ (by rfl)
  have c9r7725_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)] := by
    let c9r7725targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)]]
    let c9r7725choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7725targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)] c9r7725choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7725targets, c9r7725choice, ?_, checked⟩
    intro S h
    simp only [c9r7725targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 15 _ (by rfl)
  have c9r7726_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)] := by
    let c9r7726targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)]]
    let c9r7726choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7726targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)] c9r7726choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7726targets, c9r7726choice, ?_, checked⟩
    intro S h
    simp only [c9r7726targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 17 _ (by rfl)
  have c9r7727_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r7727targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r7727choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7727targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)] c9r7727choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7727targets, c9r7727choice, ?_, checked⟩
    intro S h
    simp only [c9r7727targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7720_closed
  · subst row; exact c9r7721_closed
  · subst row; exact c9r7722_closed
  · subst row; exact c9r7723_closed
  · subst row; exact c9r7724_closed
  · subst row; exact c9r7725_closed
  · subst row; exact c9r7726_closed
  · subst row; exact c9r7727_closed
theorem C9R07712G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7728_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r7728targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r7728choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7728targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)] c9r7728choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7728targets, c9r7728choice, ?_, checked⟩
    intro S h
    simp only [c9r7728targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 24 _ (by rfl)
  have c9r7729_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r7729targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r7729choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7729targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)] c9r7729choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7729targets, c9r7729choice, ?_, checked⟩
    intro S h
    simp only [c9r7729targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 26 _ (by rfl)
  have c9r7730_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r7730targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r7730choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7730targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)] c9r7730choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7730targets, c9r7730choice, ?_, checked⟩
    intro S h
    simp only [c9r7730targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 29 _ (by rfl)
  have c9r7731_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r7731targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r7731choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7731targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)] c9r7731choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7731targets, c9r7731choice, ?_, checked⟩
    intro S h
    simp only [c9r7731targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 0 _ (by rfl)
  have c9r7732_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r7732targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r7732choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7732targets [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)] c9r7732choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7732targets, c9r7732choice, ?_, checked⟩
    intro S h
    simp only [c9r7732targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 3 _ (by rfl)
  have c9r7733_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r7733targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r7733choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7733targets [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r7733choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7733targets, c9r7733choice, ?_, checked⟩
    intro S h
    simp only [c9r7733targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 8 _ (by rfl)
  have c9r7734_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r7734targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r7734choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7734targets [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)] c9r7734choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7734targets, c9r7734choice, ?_, checked⟩
    intro S h
    simp only [c9r7734targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 13 _ (by rfl)
  have c9r7735_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c9r7735targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c9r7735choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7735targets [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)] c9r7735choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7735targets, c9r7735choice, ?_, checked⟩
    intro S h
    simp only [c9r7735targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7728_closed
  · subst row; exact c9r7729_closed
  · subst row; exact c9r7730_closed
  · subst row; exact c9r7731_closed
  · subst row; exact c9r7732_closed
  · subst row; exact c9r7733_closed
  · subst row; exact c9r7734_closed
  · subst row; exact c9r7735_closed
theorem C9R07712G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7736_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c9r7736targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c9r7736choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7736targets [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)] c9r7736choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7736targets, c9r7736choice, ?_, checked⟩
    intro S h
    simp only [c9r7736targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 17 _ (by rfl)
  have c9r7737_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)] := by
    let c9r7737targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)]]
    let c9r7737choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7737targets [(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)] c9r7737choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7737targets, c9r7737choice, ?_, checked⟩
    intro S h
    simp only [c9r7737targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 21 _ (by rfl)
  have c9r7738_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r7738targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r7738choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7738targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)] c9r7738choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7738targets, c9r7738choice, ?_, checked⟩
    intro S h
    simp only [c9r7738targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 29 _ (by rfl)
  have c9r7739_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r7739targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r7739choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7739targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)] c9r7739choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7739targets, c9r7739choice, ?_, checked⟩
    intro S h
    simp only [c9r7739targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 0 _ (by rfl)
  have c9r7740_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r7740targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r7740choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7740targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)] c9r7740choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7740targets, c9r7740choice, ?_, checked⟩
    intro S h
    simp only [c9r7740targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 2 _ (by rfl)
  have c9r7741_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r7741targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r7741choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7741targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)] c9r7741choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7741targets, c9r7741choice, ?_, checked⟩
    intro S h
    simp only [c9r7741targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 4 _ (by rfl)
  have c9r7742_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)] := by
    let c9r7742targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)]]
    let c9r7742choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7742targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)] c9r7742choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7742targets, c9r7742choice, ?_, checked⟩
    intro S h
    simp only [c9r7742targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 7 _ (by rfl)
  have c9r7743_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)] := by
    let c9r7743targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)]]
    let c9r7743choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7743targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)] c9r7743choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7743targets, c9r7743choice, ?_, checked⟩
    intro S h
    simp only [c9r7743targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7736_closed
  · subst row; exact c9r7737_closed
  · subst row; exact c9r7738_closed
  · subst row; exact c9r7739_closed
  · subst row; exact c9r7740_closed
  · subst row; exact c9r7741_closed
  · subst row; exact c9r7742_closed
  · subst row; exact c9r7743_closed
theorem C9R07712_closed (row : List GridPoint) (h : FamilyMember row F9B003L49) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L49, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R07712G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07712G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07712G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07712G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07712G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07712G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07712G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07712G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07712G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07712G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07712G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07712G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07712G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07712G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07712G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07712G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07712G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07712G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07712G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07712G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07712G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07712G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07712G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07712G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07712G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07712G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07712G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07712G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07712G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07712G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07712G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07712G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
