import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08576G0 (row : List GridPoint) (h : row ∈ [[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8576_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)] := by
    let c9r8576targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)]]
    let c9r8576choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8576targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)] c9r8576choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8576targets, c9r8576choice, ?_, checked⟩
    intro S h
    simp only [c9r8576targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 0 _ (by rfl)
  have c9r8577_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)] := by
    let c9r8577targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)]]
    let c9r8577choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8577targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)] c9r8577choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8577targets, c9r8577choice, ?_, checked⟩
    intro S h
    simp only [c9r8577targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 2 _ (by rfl)
  have c9r8578_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)] := by
    let c9r8578targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)]]
    let c9r8578choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8578targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)] c9r8578choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8578targets, c9r8578choice, ?_, checked⟩
    intro S h
    simp only [c9r8578targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 7 _ (by rfl)
  have c9r8579_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)] := by
    let c9r8579targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,3)]]
    let c9r8579choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8579targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)] c9r8579choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8579targets, c9r8579choice, ?_, checked⟩
    intro S h
    simp only [c9r8579targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 11 _ (by rfl)
  have c9r8580_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)] := by
    let c9r8580targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,4)]]
    let c9r8580choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8580targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)] c9r8580choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8580targets, c9r8580choice, ?_, checked⟩
    intro S h
    simp only [c9r8580targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 14 _ (by rfl)
  have c9r8581_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)] := by
    let c9r8581targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,5)]]
    let c9r8581choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8581targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)] c9r8581choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8581targets, c9r8581choice, ?_, checked⟩
    intro S h
    simp only [c9r8581targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 17 _ (by rfl)
  have c9r8582_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)] := by
    let c9r8582targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(4,1)]]
    let c9r8582choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8582targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)] c9r8582choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8582targets, c9r8582choice, ?_, checked⟩
    intro S h
    simp only [c9r8582targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 20 _ (by rfl)
  have c9r8583_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)] := by
    let c9r8583targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)]]
    let c9r8583choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8583targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)] c9r8583choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8583targets, c9r8583choice, ?_, checked⟩
    intro S h
    simp only [c9r8583targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8576_closed
  · subst row; exact c9r8577_closed
  · subst row; exact c9r8578_closed
  · subst row; exact c9r8579_closed
  · subst row; exact c9r8580_closed
  · subst row; exact c9r8581_closed
  · subst row; exact c9r8582_closed
  · subst row; exact c9r8583_closed
theorem C9R08576G1 (row : List GridPoint) (h : row ∈ [[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8584_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)] := by
    let c9r8584targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,4)]]
    let c9r8584choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8584targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)] c9r8584choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8584targets, c9r8584choice, ?_, checked⟩
    intro S h
    simp only [c9r8584targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 27 _ (by rfl)
  have c9r8585_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)] := by
    let c9r8585targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,5)]]
    let c9r8585choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8585targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)] c9r8585choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8585targets, c9r8585choice, ?_, checked⟩
    intro S h
    simp only [c9r8585targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 30 _ (by rfl)
  have c9r8586_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)] := by
    let c9r8586targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(4,2)]]
    let c9r8586choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8586targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)] c9r8586choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8586targets, c9r8586choice, ?_, checked⟩
    intro S h
    simp only [c9r8586targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 1 _ (by rfl)
  have c9r8587_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)] := by
    let c9r8587targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)]]
    let c9r8587choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8587targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)] c9r8587choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8587targets, c9r8587choice, ?_, checked⟩
    intro S h
    simp only [c9r8587targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 4 _ (by rfl)
  have c9r8588_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)] := by
    let c9r8588targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)]]
    let c9r8588choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8588targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)] c9r8588choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8588targets, c9r8588choice, ?_, checked⟩
    intro S h
    simp only [c9r8588targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 7 _ (by rfl)
  have c9r8589_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)] := by
    let c9r8589targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)]]
    let c9r8589choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8589targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)] c9r8589choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8589targets, c9r8589choice, ?_, checked⟩
    intro S h
    simp only [c9r8589targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 10 _ (by rfl)
  have c9r8590_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)] := by
    let c9r8590targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)]]
    let c9r8590choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8590targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)] c9r8590choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8590targets, c9r8590choice, ?_, checked⟩
    intro S h
    simp only [c9r8590targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 13 _ (by rfl)
  have c9r8591_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)] := by
    let c9r8591targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4)]]
    let c9r8591choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8591targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)] c9r8591choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8591targets, c9r8591choice, ?_, checked⟩
    intro S h
    simp only [c9r8591targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8584_closed
  · subst row; exact c9r8585_closed
  · subst row; exact c9r8586_closed
  · subst row; exact c9r8587_closed
  · subst row; exact c9r8588_closed
  · subst row; exact c9r8589_closed
  · subst row; exact c9r8590_closed
  · subst row; exact c9r8591_closed
theorem C9R08576G2 (row : List GridPoint) (h : row ∈ [[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8592_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)] := by
    let c9r8592targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(3,6)]]
    let c9r8592choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8592targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)] c9r8592choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8592targets, c9r8592choice, ?_, checked⟩
    intro S h
    simp only [c9r8592targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 19 _ (by rfl)
  have c9r8593_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)] := by
    let c9r8593targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5),(4,5)]]
    let c9r8593choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8593targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)] c9r8593choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8593targets, c9r8593choice, ?_, checked⟩
    intro S h
    simp only [c9r8593targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 22 _ (by rfl)
  have c9r8594_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r8594targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r8594choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r8594targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c9r8594choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8594targets, c9r8594choice, ?_, checked⟩
    intro S h
    simp only [c9r8594targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 28 _ (by rfl)
  have c9r8595_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] := by
    let c9r8595targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)]]
    let c9r8595choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r8595targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] c9r8595choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8595targets, c9r8595choice, ?_, checked⟩
    intro S h
    simp only [c9r8595targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 0 _ (by rfl)
  have c9r8596_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] := by
    let c9r8596targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)]]
    let c9r8596choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8596targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] c9r8596choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8596targets, c9r8596choice, ?_, checked⟩
    intro S h
    simp only [c9r8596targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 4 _ (by rfl)
  have c9r8597_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] := by
    let c9r8597targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c9r8597choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8597targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] c9r8597choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8597targets, c9r8597choice, ?_, checked⟩
    intro S h
    simp only [c9r8597targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 6 _ (by rfl)
  have c9r8598_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c9r8598targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c9r8598choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8598targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] c9r8598choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8598targets, c9r8598choice, ?_, checked⟩
    intro S h
    simp only [c9r8598targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 8 _ (by rfl)
  have c9r8599_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)] := by
    let c9r8599targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,3)]]
    let c9r8599choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r8599targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)] c9r8599choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8599targets, c9r8599choice, ?_, checked⟩
    intro S h
    simp only [c9r8599targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8592_closed
  · subst row; exact c9r8593_closed
  · subst row; exact c9r8594_closed
  · subst row; exact c9r8595_closed
  · subst row; exact c9r8596_closed
  · subst row; exact c9r8597_closed
  · subst row; exact c9r8598_closed
  · subst row; exact c9r8599_closed
theorem C9R08576G3 (row : List GridPoint) (h : row ∈ [[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8600_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)] := by
    let c9r8600targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,4)]]
    let c9r8600choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8600targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)] c9r8600choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8600targets, c9r8600choice, ?_, checked⟩
    intro S h
    simp only [c9r8600targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 16 _ (by rfl)
  have c9r8601_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)] := by
    let c9r8601targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(4,0)]]
    let c9r8601choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8601targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)] c9r8601choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8601targets, c9r8601choice, ?_, checked⟩
    intro S h
    simp only [c9r8601targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 19 _ (by rfl)
  have c9r8602_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)] := by
    let c9r8602targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2),(4,2)]]
    let c9r8602choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8602targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)] c9r8602choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8602targets, c9r8602choice, ?_, checked⟩
    intro S h
    simp only [c9r8602targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 22 _ (by rfl)
  have c9r8603_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)] := by
    let c9r8603targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,4)]]
    let c9r8603choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8603targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)] c9r8603choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8603targets, c9r8603choice, ?_, checked⟩
    intro S h
    simp only [c9r8603targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 26 _ (by rfl)
  have c9r8604_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)] := by
    let c9r8604targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0)]]
    let c9r8604choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8604targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)] c9r8604choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8604targets, c9r8604choice, ?_, checked⟩
    intro S h
    simp only [c9r8604targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 29 _ (by rfl)
  have c9r8605_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)] := by
    let c9r8605targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3)]]
    let c9r8605choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8605targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)] c9r8605choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8605targets, c9r8605choice, ?_, checked⟩
    intro S h
    simp only [c9r8605targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 0 _ (by rfl)
  have c9r8606_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)] := by
    let c9r8606targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5)]]
    let c9r8606choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8606targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)] c9r8606choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8606targets, c9r8606choice, ?_, checked⟩
    intro S h
    simp only [c9r8606targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 4 _ (by rfl)
  have c9r8607_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)] := by
    let c9r8607targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0)]]
    let c9r8607choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8607targets [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)] c9r8607choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8607targets, c9r8607choice, ?_, checked⟩
    intro S h
    simp only [c9r8607targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,false] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8600_closed
  · subst row; exact c9r8601_closed
  · subst row; exact c9r8602_closed
  · subst row; exact c9r8603_closed
  · subst row; exact c9r8604_closed
  · subst row; exact c9r8605_closed
  · subst row; exact c9r8606_closed
  · subst row; exact c9r8607_closed
theorem C9R08576_closed (row : List GridPoint) (h : FamilyMember row F9B004L12) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L12, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08576G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08576G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08576G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08576G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08576G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08576G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08576G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08576G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08576G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08576G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08576G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08576G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08576G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08576G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08576G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08576G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08576G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08576G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08576G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08576G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08576G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08576G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08576G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08576G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08576G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08576G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08576G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08576G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08576G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08576G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08576G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08576G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
