import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R04928G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4928_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] := by
    let c9r4928targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)]]
    let c9r4928choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4928targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] c9r4928choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4928targets, c9r4928choice, ?_, checked⟩
    intro S h
    simp only [c9r4928targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 17 _ (by rfl)
  have c9r4929_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c9r4929targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c9r4929choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4929targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c9r4929choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4929targets, c9r4929choice, ?_, checked⟩
    intro S h
    simp only [c9r4929targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 22 _ (by rfl)
  have c9r4930_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)] := by
    let c9r4930targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)]]
    let c9r4930choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4930targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)] c9r4930choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4930targets, c9r4930choice, ?_, checked⟩
    intro S h
    simp only [c9r4930targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 26 _ (by rfl)
  have c9r4931_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)] := by
    let c9r4931targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)]]
    let c9r4931choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4931targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)] c9r4931choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4931targets, c9r4931choice, ?_, checked⟩
    intro S h
    simp only [c9r4931targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 29 _ (by rfl)
  have c9r4932_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)] := by
    let c9r4932targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)]]
    let c9r4932choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4932targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)] c9r4932choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4932targets, c9r4932choice, ?_, checked⟩
    intro S h
    simp only [c9r4932targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 0 _ (by rfl)
  have c9r4933_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)] := by
    let c9r4933targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)]]
    let c9r4933choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4933targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)] c9r4933choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4933targets, c9r4933choice, ?_, checked⟩
    intro S h
    simp only [c9r4933targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 2 _ (by rfl)
  have c9r4934_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)] := by
    let c9r4934targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)]]
    let c9r4934choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4934targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)] c9r4934choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4934targets, c9r4934choice, ?_, checked⟩
    intro S h
    simp only [c9r4934targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 6 _ (by rfl)
  have c9r4935_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)] := by
    let c9r4935targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)]]
    let c9r4935choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4935targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)] c9r4935choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4935targets, c9r4935choice, ?_, checked⟩
    intro S h
    simp only [c9r4935targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4928_closed
  · subst row; exact c9r4929_closed
  · subst row; exact c9r4930_closed
  · subst row; exact c9r4931_closed
  · subst row; exact c9r4932_closed
  · subst row; exact c9r4933_closed
  · subst row; exact c9r4934_closed
  · subst row; exact c9r4935_closed
theorem C9R04928G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4936_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)] := by
    let c9r4936targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)]]
    let c9r4936choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4936targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)] c9r4936choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4936targets, c9r4936choice, ?_, checked⟩
    intro S h
    simp only [c9r4936targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 12 _ (by rfl)
  have c9r4937_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)] := by
    let c9r4937targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)]]
    let c9r4937choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4937targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)] c9r4937choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4937targets, c9r4937choice, ?_, checked⟩
    intro S h
    simp only [c9r4937targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 15 _ (by rfl)
  have c9r4938_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)] := by
    let c9r4938targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)]]
    let c9r4938choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4938targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)] c9r4938choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4938targets, c9r4938choice, ?_, checked⟩
    intro S h
    simp only [c9r4938targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 18 _ (by rfl)
  have c9r4939_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)] := by
    let c9r4939targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)]]
    let c9r4939choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4939targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)] c9r4939choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4939targets, c9r4939choice, ?_, checked⟩
    intro S h
    simp only [c9r4939targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 21 _ (by rfl)
  have c9r4940_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)] := by
    let c9r4940targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)]]
    let c9r4940choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4940targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)] c9r4940choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4940targets, c9r4940choice, ?_, checked⟩
    intro S h
    simp only [c9r4940targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 24 _ (by rfl)
  have c9r4941_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)] := by
    let c9r4941targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]]
    let c9r4941choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4941targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)] c9r4941choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4941targets, c9r4941choice, ?_, checked⟩
    intro S h
    simp only [c9r4941targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 27 _ (by rfl)
  have c9r4942_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)] := by
    let c9r4942targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)]]
    let c9r4942choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4942targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)] c9r4942choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4942targets, c9r4942choice, ?_, checked⟩
    intro S h
    simp only [c9r4942targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 30 _ (by rfl)
  have c9r4943_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)] := by
    let c9r4943targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)]]
    let c9r4943choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4943targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)] c9r4943choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4943targets, c9r4943choice, ?_, checked⟩
    intro S h
    simp only [c9r4943targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4936_closed
  · subst row; exact c9r4937_closed
  · subst row; exact c9r4938_closed
  · subst row; exact c9r4939_closed
  · subst row; exact c9r4940_closed
  · subst row; exact c9r4941_closed
  · subst row; exact c9r4942_closed
  · subst row; exact c9r4943_closed
theorem C9R04928G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4944_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)] := by
    let c9r4944targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)]]
    let c9r4944choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4944targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)] c9r4944choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4944targets, c9r4944choice, ?_, checked⟩
    intro S h
    simp only [c9r4944targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 4 _ (by rfl)
  have c9r4945_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] := by
    let c9r4945targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c9r4945choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4945targets [(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] c9r4945choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4945targets, c9r4945choice, ?_, checked⟩
    intro S h
    simp only [c9r4945targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 11 _ (by rfl)
  have c9r4946_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] := by
    let c9r4946targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)]]
    let c9r4946choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4946targets [(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] c9r4946choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4946targets, c9r4946choice, ?_, checked⟩
    intro S h
    simp only [c9r4946targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 17 _ (by rfl)
  have c9r4947_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r4947targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r4947choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4947targets [(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)] c9r4947choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4947targets, c9r4947choice, ?_, checked⟩
    intro S h
    simp only [c9r4947targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 24 _ (by rfl)
  have c9r4948_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] := by
    let c9r4948targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)]]
    let c9r4948choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4948targets [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] c9r4948choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4948targets, c9r4948choice, ?_, checked⟩
    intro S h
    simp only [c9r4948targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 31 _ (by rfl)
  have c9r4949_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r4949targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r4949choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4949targets [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c9r4949choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4949targets, c9r4949choice, ?_, checked⟩
    intro S h
    simp only [c9r4949targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 5 _ (by rfl)
  have c9r4950_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] := by
    let c9r4950targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)]]
    let c9r4950choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4950targets [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] c9r4950choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4950targets, c9r4950choice, ?_, checked⟩
    intro S h
    simp only [c9r4950targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 9 _ (by rfl)
  have c9r4951_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] := by
    let c9r4951targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)]]
    let c9r4951choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4951targets [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] c9r4951choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4951targets, c9r4951choice, ?_, checked⟩
    intro S h
    simp only [c9r4951targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4944_closed
  · subst row; exact c9r4945_closed
  · subst row; exact c9r4946_closed
  · subst row; exact c9r4947_closed
  · subst row; exact c9r4948_closed
  · subst row; exact c9r4949_closed
  · subst row; exact c9r4950_closed
  · subst row; exact c9r4951_closed
theorem C9R04928G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4952_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] := by
    let c9r4952targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c9r4952choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4952targets [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] c9r4952choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4952targets, c9r4952choice, ?_, checked⟩
    intro S h
    simp only [c9r4952targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 15 _ (by rfl)
  have c9r4953_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c9r4953targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c9r4953choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4953targets [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] c9r4953choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4953targets, c9r4953choice, ?_, checked⟩
    intro S h
    simp only [c9r4953targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 17 _ (by rfl)
  have c9r4954_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] := by
    let c9r4954targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)]]
    let c9r4954choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4954targets [(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] c9r4954choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4954targets, c9r4954choice, ?_, checked⟩
    intro S h
    simp only [c9r4954targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 23 _ (by rfl)
  have c9r4955_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r4955targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,1),(1,4),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(0,5),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,4),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,5),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r4955choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4955targets [(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] c9r4955choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4955targets, c9r4955choice, ?_, checked⟩
    intro S h
    simp only [c9r4955targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 0 _ (by rfl)
  have c9r4956_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r4956targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,1),(1,4),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,4),(1,1),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,5),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r4956choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4956targets [(0,1),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r4956choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4956targets, c9r4956choice, ?_, checked⟩
    intro S h
    simp only [c9r4956targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 8 _ (by rfl)
  have c9r4957_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c9r4957targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,1),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,1),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c9r4957choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4957targets [(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c9r4957choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4957targets, c9r4957choice, ?_, checked⟩
    intro S h
    simp only [c9r4957targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 17 _ (by rfl)
  have c9r4958_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c9r4958targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,5),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c9r4958choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4958targets [(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c9r4958choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4958targets, c9r4958choice, ?_, checked⟩
    intro S h
    simp only [c9r4958targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 26 _ (by rfl)
  have c9r4959_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] := by
    let c9r4959targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,5),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,2),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)]]
    let c9r4959choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4959targets [(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] c9r4959choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4959targets, c9r4959choice, ?_, checked⟩
    intro S h
    simp only [c9r4959targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,true] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4952_closed
  · subst row; exact c9r4953_closed
  · subst row; exact c9r4954_closed
  · subst row; exact c9r4955_closed
  · subst row; exact c9r4956_closed
  · subst row; exact c9r4957_closed
  · subst row; exact c9r4958_closed
  · subst row; exact c9r4959_closed
theorem C9R04928_closed (row : List GridPoint) (h : FamilyMember row F9B002L26) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L26, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R04928G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04928G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04928G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04928G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04928G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04928G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04928G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04928G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04928G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04928G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04928G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04928G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04928G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04928G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04928G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04928G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04928G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04928G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04928G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04928G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04928G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04928G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04928G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04928G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04928G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04928G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04928G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04928G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04928G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04928G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04928G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04928G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
