import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R07104G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7104_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] := by
    let c9r7104targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c9r7104choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7104targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] c9r7104choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7104targets, c9r7104choice, ?_, checked⟩
    intro S h
    simp only [c9r7104targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 1 _ (by rfl)
  have c9r7105_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c9r7105targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c9r7105choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7105targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] c9r7105choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7105targets, c9r7105choice, ?_, checked⟩
    intro S h
    simp only [c9r7105targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 3 _ (by rfl)
  have c9r7106_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)] := by
    let c9r7106targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,3)]]
    let c9r7106choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7106targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)] c9r7106choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7106targets, c9r7106choice, ?_, checked⟩
    intro S h
    simp only [c9r7106targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 7 _ (by rfl)
  have c9r7107_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)] := by
    let c9r7107targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,4)]]
    let c9r7107choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7107targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)] c9r7107choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7107targets, c9r7107choice, ?_, checked⟩
    intro S h
    simp only [c9r7107targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 11 _ (by rfl)
  have c9r7108_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)] := by
    let c9r7108targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(4,0)]]
    let c9r7108choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7108targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)] c9r7108choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7108targets, c9r7108choice, ?_, checked⟩
    intro S h
    simp only [c9r7108targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 14 _ (by rfl)
  have c9r7109_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)] := by
    let c9r7109targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2),(4,2)]]
    let c9r7109choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7109targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)] c9r7109choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7109targets, c9r7109choice, ?_, checked⟩
    intro S h
    simp only [c9r7109targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 17 _ (by rfl)
  have c9r7110_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)] := by
    let c9r7110targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,4)]]
    let c9r7110choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7110targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)] c9r7110choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7110targets, c9r7110choice, ?_, checked⟩
    intro S h
    simp only [c9r7110targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 21 _ (by rfl)
  have c9r7111_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)] := by
    let c9r7111targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0)]]
    let c9r7111choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7111targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)] c9r7111choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7111targets, c9r7111choice, ?_, checked⟩
    intro S h
    simp only [c9r7111targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7104_closed
  · subst row; exact c9r7105_closed
  · subst row; exact c9r7106_closed
  · subst row; exact c9r7107_closed
  · subst row; exact c9r7108_closed
  · subst row; exact c9r7109_closed
  · subst row; exact c9r7110_closed
  · subst row; exact c9r7111_closed
theorem C9R07104G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7112_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)] := by
    let c9r7112targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3)]]
    let c9r7112choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7112targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)] c9r7112choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7112targets, c9r7112choice, ?_, checked⟩
    intro S h
    simp only [c9r7112targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 27 _ (by rfl)
  have c9r7113_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)] := by
    let c9r7113targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5)]]
    let c9r7113choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7113targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)] c9r7113choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7113targets, c9r7113choice, ?_, checked⟩
    intro S h
    simp only [c9r7113targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 31 _ (by rfl)
  have c9r7114_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)] := by
    let c9r7114targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0)]]
    let c9r7114choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7114targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)] c9r7114choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7114targets, c9r7114choice, ?_, checked⟩
    intro S h
    simp only [c9r7114targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 2 _ (by rfl)
  have c9r7115_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)] := by
    let c9r7115targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4)]]
    let c9r7115choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7115targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)] c9r7115choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7115targets, c9r7115choice, ?_, checked⟩
    intro S h
    simp only [c9r7115targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 5 _ (by rfl)
  have c9r7116_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)] := by
    let c9r7116targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1)]]
    let c9r7116choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7116targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)] c9r7116choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7116targets, c9r7116choice, ?_, checked⟩
    intro S h
    simp only [c9r7116targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 8 _ (by rfl)
  have c9r7117_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)] := by
    let c9r7117targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0),(5,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0)]]
    let c9r7117choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r7117targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)] c9r7117choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7117targets, c9r7117choice, ?_, checked⟩
    intro S h
    simp only [c9r7117targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 10 _ (by rfl)
  have c9r7118_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)] := by
    let c9r7118targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)]]
    let c9r7118choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7118targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)] c9r7118choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7118targets, c9r7118choice, ?_, checked⟩
    intro S h
    simp only [c9r7118targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
  have c9r7119_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)] := by
    let c9r7119targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,4)]]
    let c9r7119choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7119targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)] c9r7119choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7119targets, c9r7119choice, ?_, checked⟩
    intro S h
    simp only [c9r7119targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7112_closed
  · subst row; exact c9r7113_closed
  · subst row; exact c9r7114_closed
  · subst row; exact c9r7115_closed
  · subst row; exact c9r7116_closed
  · subst row; exact c9r7117_closed
  · subst row; exact c9r7118_closed
  · subst row; exact c9r7119_closed
theorem C9R07104G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7120_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)] := by
    let c9r7120targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1)]]
    let c9r7120choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7120targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)] c9r7120choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7120targets, c9r7120choice, ?_, checked⟩
    intro S h
    simp only [c9r7120targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
  have c9r7121_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)] := by
    let c9r7121targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(4,2)]]
    let c9r7121choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7121targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)] c9r7121choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7121targets, c9r7121choice, ?_, checked⟩
    intro S h
    simp only [c9r7121targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 23 _ (by rfl)
  have c9r7122_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)] := by
    let c9r7122targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,4)]]
    let c9r7122choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7122targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)] c9r7122choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7122targets, c9r7122choice, ?_, checked⟩
    intro S h
    simp only [c9r7122targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 27 _ (by rfl)
  have c9r7123_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)] := by
    let c9r7123targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(4,1)]]
    let c9r7123choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7123targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)] c9r7123choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7123targets, c9r7123choice, ?_, checked⟩
    intro S h
    simp only [c9r7123targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 31 _ (by rfl)
  have c9r7124_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)] := by
    let c9r7124targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(4,3)]]
    let c9r7124choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7124targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)] c9r7124choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7124targets, c9r7124choice, ?_, checked⟩
    intro S h
    simp only [c9r7124targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
  have c9r7125_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)] := by
    let c9r7125targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,5)]]
    let c9r7125choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7125targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)] c9r7125choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7125targets, c9r7125choice, ?_, checked⟩
    intro S h
    simp only [c9r7125targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
  have c9r7126_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)] := by
    let c9r7126targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,1)]]
    let c9r7126choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7126targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)] c9r7126choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7126targets, c9r7126choice, ?_, checked⟩
    intro S h
    simp only [c9r7126targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 10 _ (by rfl)
  have c9r7127_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)] := by
    let c9r7127targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(4,4)]]
    let c9r7127choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7127targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)] c9r7127choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7127targets, c9r7127choice, ?_, checked⟩
    intro S h
    simp only [c9r7127targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7120_closed
  · subst row; exact c9r7121_closed
  · subst row; exact c9r7122_closed
  · subst row; exact c9r7123_closed
  · subst row; exact c9r7124_closed
  · subst row; exact c9r7125_closed
  · subst row; exact c9r7126_closed
  · subst row; exact c9r7127_closed
theorem C9R07104G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7128_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] := by
    let c9r7128targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)]]
    let c9r7128choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7128targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] c9r7128choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7128targets, c9r7128choice, ?_, checked⟩
    intro S h
    simp only [c9r7128targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
  have c9r7129_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)] := by
    let c9r7129targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,2)]]
    let c9r7129choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7129targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)] c9r7129choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7129targets, c9r7129choice, ?_, checked⟩
    intro S h
    simp only [c9r7129targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 19 _ (by rfl)
  have c9r7130_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)] := by
    let c9r7130targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(5,1)]]
    let c9r7130choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7130targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)] c9r7130choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7130targets, c9r7130choice, ?_, checked⟩
    intro S h
    simp only [c9r7130targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 22 _ (by rfl)
  have c9r7131_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)] := by
    let c9r7131targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c9r7131choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7131targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)] c9r7131choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7131targets, c9r7131choice, ?_, checked⟩
    intro S h
    simp only [c9r7131targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 26 _ (by rfl)
  have c9r7132_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)] := by
    let c9r7132targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)]]
    let c9r7132choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7132targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)] c9r7132choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7132targets, c9r7132choice, ?_, checked⟩
    intro S h
    simp only [c9r7132targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 29 _ (by rfl)
  have c9r7133_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)] := by
    let c9r7133targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)]]
    let c9r7133choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7133targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)] c9r7133choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7133targets, c9r7133choice, ?_, checked⟩
    intro S h
    simp only [c9r7133targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 31 _ (by rfl)
  have c9r7134_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)] := by
    let c9r7134targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)]]
    let c9r7134choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7134targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)] c9r7134choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7134targets, c9r7134choice, ?_, checked⟩
    intro S h
    simp only [c9r7134targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 3 _ (by rfl)
  have c9r7135_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)] := by
    let c9r7135targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)]]
    let c9r7135choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7135targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)] c9r7135choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7135targets, c9r7135choice, ?_, checked⟩
    intro S h
    simp only [c9r7135targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7128_closed
  · subst row; exact c9r7129_closed
  · subst row; exact c9r7130_closed
  · subst row; exact c9r7131_closed
  · subst row; exact c9r7132_closed
  · subst row; exact c9r7133_closed
  · subst row; exact c9r7134_closed
  · subst row; exact c9r7135_closed
theorem C9R07104_closed (row : List GridPoint) (h : FamilyMember row F9B003L30) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L30, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R07104G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07104G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07104G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07104G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07104G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07104G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07104G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07104G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07104G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07104G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07104G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07104G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07104G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07104G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07104G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07104G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07104G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07104G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07104G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07104G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07104G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07104G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07104G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07104G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07104G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07104G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07104G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07104G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07104G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07104G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07104G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07104G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
