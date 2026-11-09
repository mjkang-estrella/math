import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06752G0 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6752_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c9r6752targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c9r6752choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6752targets [(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] c9r6752choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6752targets, c9r6752choice, ?_, checked⟩
    intro S h
    simp only [c9r6752targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 14 _ (by rfl)
  have c9r6753_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] := by
    let c9r6753targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)]]
    let c9r6753choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6753targets [(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] c9r6753choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6753targets, c9r6753choice, ?_, checked⟩
    intro S h
    simp only [c9r6753targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 20 _ (by rfl)
  have c9r6754_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r6754targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r6754choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6754targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r6754choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6754targets, c9r6754choice, ?_, checked⟩
    intro S h
    simp only [c9r6754targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 27 _ (by rfl)
  have c9r6755_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r6755targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r6755choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6755targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c9r6755choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6755targets, c9r6755choice, ?_, checked⟩
    intro S h
    simp only [c9r6755targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 30 _ (by rfl)
  have c9r6756_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r6756targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r6756choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))))))
    have checked : successorFastRowCheck c9r6756targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] c9r6756choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6756targets, c9r6756choice, ?_, checked⟩
    intro S h
    simp only [c9r6756targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 0 _ (by rfl)
  have c9r6757_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r6757targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r6757choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6757targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] c9r6757choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6757targets, c9r6757choice, ?_, checked⟩
    intro S h
    simp only [c9r6757targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 2 _ (by rfl)
  have c9r6758_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] := by
    let c9r6758targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)]]
    let c9r6758choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6758targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] c9r6758choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6758targets, c9r6758choice, ?_, checked⟩
    intro S h
    simp only [c9r6758targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 7 _ (by rfl)
  have c9r6759_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] := by
    let c9r6759targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)]]
    let c9r6759choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6759targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] c9r6759choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6759targets, c9r6759choice, ?_, checked⟩
    intro S h
    simp only [c9r6759targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6752_closed
  · subst row; exact c9r6753_closed
  · subst row; exact c9r6754_closed
  · subst row; exact c9r6755_closed
  · subst row; exact c9r6756_closed
  · subst row; exact c9r6757_closed
  · subst row; exact c9r6758_closed
  · subst row; exact c9r6759_closed
theorem C9R06752G1 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6760_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] := by
    let c9r6760targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)]]
    let c9r6760choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6760targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] c9r6760choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6760targets, c9r6760choice, ?_, checked⟩
    intro S h
    simp only [c9r6760targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 13 _ (by rfl)
  have c9r6761_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)] := by
    let c9r6761targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)]]
    let c9r6761choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6761targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)] c9r6761choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6761targets, c9r6761choice, ?_, checked⟩
    intro S h
    simp only [c9r6761targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 16 _ (by rfl)
  have c9r6762_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)] := by
    let c9r6762targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c9r6762choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6762targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)] c9r6762choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6762targets, c9r6762choice, ?_, checked⟩
    intro S h
    simp only [c9r6762targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 19 _ (by rfl)
  have c9r6763_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)] := by
    let c9r6763targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c9r6763choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6763targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)] c9r6763choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6763targets, c9r6763choice, ?_, checked⟩
    intro S h
    simp only [c9r6763targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 21 _ (by rfl)
  have c9r6764_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)] := by
    let c9r6764targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c9r6764choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6764targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)] c9r6764choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6764targets, c9r6764choice, ?_, checked⟩
    intro S h
    simp only [c9r6764targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 24 _ (by rfl)
  have c9r6765_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)] := by
    let c9r6765targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c9r6765choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6765targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)] c9r6765choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6765targets, c9r6765choice, ?_, checked⟩
    intro S h
    simp only [c9r6765targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 27 _ (by rfl)
  have c9r6766_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r6766targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r6766choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6766targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)] c9r6766choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6766targets, c9r6766choice, ?_, checked⟩
    intro S h
    simp only [c9r6766targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 0 _ (by rfl)
  have c9r6767_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)] := by
    let c9r6767targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)]]
    let c9r6767choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6767targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)] c9r6767choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6767targets, c9r6767choice, ?_, checked⟩
    intro S h
    simp only [c9r6767targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6760_closed
  · subst row; exact c9r6761_closed
  · subst row; exact c9r6762_closed
  · subst row; exact c9r6763_closed
  · subst row; exact c9r6764_closed
  · subst row; exact c9r6765_closed
  · subst row; exact c9r6766_closed
  · subst row; exact c9r6767_closed
theorem C9R06752G2 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6768_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)] := by
    let c9r6768targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6768choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6768targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)] c9r6768choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6768targets, c9r6768choice, ?_, checked⟩
    intro S h
    simp only [c9r6768targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 11 _ (by rfl)
  have c9r6769_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)] := by
    let c9r6769targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c9r6769choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6769targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)] c9r6769choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6769targets, c9r6769choice, ?_, checked⟩
    intro S h
    simp only [c9r6769targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 13 _ (by rfl)
  have c9r6770_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)] := by
    let c9r6770targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c9r6770choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6770targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)] c9r6770choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6770targets, c9r6770choice, ?_, checked⟩
    intro S h
    simp only [c9r6770targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 15 _ (by rfl)
  have c9r6771_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)] := by
    let c9r6771targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c9r6771choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6771targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)] c9r6771choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6771targets, c9r6771choice, ?_, checked⟩
    intro S h
    simp only [c9r6771targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 19 _ (by rfl)
  have c9r6772_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r6772targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6772choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6772targets [(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] c9r6772choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6772targets, c9r6772choice, ?_, checked⟩
    intro S h
    simp only [c9r6772targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 25 _ (by rfl)
  have c9r6773_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r6773targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r6773choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6773targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r6773choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6773targets, c9r6773choice, ?_, checked⟩
    intro S h
    simp only [c9r6773targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 3 _ (by rfl)
  have c9r6774_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r6774targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r6774choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6774targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r6774choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6774targets, c9r6774choice, ?_, checked⟩
    intro S h
    simp only [c9r6774targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 7 _ (by rfl)
  have c9r6775_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r6775targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r6775choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6775targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r6775choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6775targets, c9r6775choice, ?_, checked⟩
    intro S h
    simp only [c9r6775targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6768_closed
  · subst row; exact c9r6769_closed
  · subst row; exact c9r6770_closed
  · subst row; exact c9r6771_closed
  · subst row; exact c9r6772_closed
  · subst row; exact c9r6773_closed
  · subst row; exact c9r6774_closed
  · subst row; exact c9r6775_closed
theorem C9R06752G3 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6776_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r6776targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r6776choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6776targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r6776choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6776targets, c9r6776choice, ?_, checked⟩
    intro S h
    simp only [c9r6776targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 12 _ (by rfl)
  have c9r6777_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r6777targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r6777choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6777targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r6777choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6777targets, c9r6777choice, ?_, checked⟩
    intro S h
    simp only [c9r6777targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 14 _ (by rfl)
  have c9r6778_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r6778targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r6778choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6778targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] c9r6778choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6778targets, c9r6778choice, ?_, checked⟩
    intro S h
    simp only [c9r6778targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 17 _ (by rfl)
  have c9r6779_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c9r6779targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c9r6779choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6779targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] c9r6779choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6779targets, c9r6779choice, ?_, checked⟩
    intro S h
    simp only [c9r6779targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 20 _ (by rfl)
  have c9r6780_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c9r6780targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c9r6780choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6780targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] c9r6780choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6780targets, c9r6780choice, ?_, checked⟩
    intro S h
    simp only [c9r6780targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 22 _ (by rfl)
  have c9r6781_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c9r6781targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c9r6781choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6781targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] c9r6781choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6781targets, c9r6781choice, ?_, checked⟩
    intro S h
    simp only [c9r6781targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 25 _ (by rfl)
  have c9r6782_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c9r6782targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c9r6782choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6782targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] c9r6782choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6782targets, c9r6782choice, ?_, checked⟩
    intro S h
    simp only [c9r6782targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 28 _ (by rfl)
  have c9r6783_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c9r6783targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c9r6783choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6783targets [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] c9r6783choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6783targets, c9r6783choice, ?_, checked⟩
    intro S h
    simp only [c9r6783targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,true,false] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6776_closed
  · subst row; exact c9r6777_closed
  · subst row; exact c9r6778_closed
  · subst row; exact c9r6779_closed
  · subst row; exact c9r6780_closed
  · subst row; exact c9r6781_closed
  · subst row; exact c9r6782_closed
  · subst row; exact c9r6783_closed
theorem C9R06752_closed (row : List GridPoint) (h : FamilyMember row F9B003L19) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L19, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06752G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06752G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06752G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06752G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06752G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06752G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06752G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06752G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06752G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06752G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06752G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06752G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06752G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06752G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06752G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06752G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06752G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06752G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06752G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06752G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06752G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06752G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06752G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06752G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06752G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06752G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06752G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06752G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06752G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06752G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06752G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06752G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
