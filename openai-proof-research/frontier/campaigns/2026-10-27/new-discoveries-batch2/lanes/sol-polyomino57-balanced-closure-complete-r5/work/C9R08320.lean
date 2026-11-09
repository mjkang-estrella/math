import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08320G0 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8320_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] := by
    let c9r8320targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(2,3)],[(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
    let c9r8320choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8320targets [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] c9r8320choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8320targets, c9r8320choice, ?_, checked⟩
    intro S h
    simp only [c9r8320targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 28 _ (by rfl)
  have c9r8321_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] := by
    let c9r8321targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(3,0)],[(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
    let c9r8321choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8321targets [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] c9r8321choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8321targets, c9r8321choice, ?_, checked⟩
    intro S h
    simp only [c9r8321targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 30 _ (by rfl)
  have c9r8322_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] := by
    let c9r8322targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(3,1)],[(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
    let c9r8322choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8322targets [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] c9r8322choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8322targets, c9r8322choice, ?_, checked⟩
    intro S h
    simp only [c9r8322targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 0 _ (by rfl)
  have c9r8323_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] := by
    let c9r8323targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)]]
    let c9r8323choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8323targets [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] c9r8323choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8323targets, c9r8323choice, ?_, checked⟩
    intro S h
    simp only [c9r8323targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 5 _ (by rfl)
  have c9r8324_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r8324targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(0,6),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r8324choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8324targets [(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r8324choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8324targets, c9r8324choice, ?_, checked⟩
    intro S h
    simp only [c9r8324targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 14 _ (by rfl)
  have c9r8325_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r8325targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,4),(0,5),(0,6),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r8325choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8325targets [(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c9r8325choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8325targets, c9r8325choice, ?_, checked⟩
    intro S h
    simp only [c9r8325targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 22 _ (by rfl)
  have c9r8326_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)] := by
    let c9r8326targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,4),(0,5),(0,6),(1,3),(1,4),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(3,2)]]
    let c9r8326choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8326targets [(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)] c9r8326choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8326targets, c9r8326choice, ?_, checked⟩
    intro S h
    simp only [c9r8326targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 30 _ (by rfl)
  have c9r8327_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r8327targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(0,6),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r8327choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8327targets [(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r8327choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8327targets, c9r8327choice, ?_, checked⟩
    intro S h
    simp only [c9r8327targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8320_closed
  · subst row; exact c9r8321_closed
  · subst row; exact c9r8322_closed
  · subst row; exact c9r8323_closed
  · subst row; exact c9r8324_closed
  · subst row; exact c9r8325_closed
  · subst row; exact c9r8326_closed
  · subst row; exact c9r8327_closed
theorem C9R08320G1 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8328_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r8328targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,4),(0,5),(0,6),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(0,5),(0,6),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r8328choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8328targets [(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c9r8328choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8328targets, c9r8328choice, ?_, checked⟩
    intro S h
    simp only [c9r8328targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 8 _ (by rfl)
  have c9r8329_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r8329targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,4),(0,5),(0,6),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r8329choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8329targets [(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] c9r8329choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8329targets, c9r8329choice, ?_, checked⟩
    intro S h
    simp only [c9r8329targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 10 _ (by rfl)
  have c9r8330_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r8330targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,4),(0,5),(0,6),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r8330choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8330targets [(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] c9r8330choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8330targets, c9r8330choice, ?_, checked⟩
    intro S h
    simp only [c9r8330targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 12 _ (by rfl)
  have c9r8331_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r8331targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,4),(0,5),(0,6),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r8331choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8331targets [(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)] c9r8331choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8331targets, c9r8331choice, ?_, checked⟩
    intro S h
    simp only [c9r8331targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 17 _ (by rfl)
  have c9r8332_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r8332targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(0,5),(0,6),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r8332choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8332targets [(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] c9r8332choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8332targets, c9r8332choice, ?_, checked⟩
    intro S h
    simp only [c9r8332targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 23 _ (by rfl)
  have c9r8333_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r8333targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(0,6),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r8333choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8333targets [(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] c9r8333choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8333targets, c9r8333choice, ?_, checked⟩
    intro S h
    simp only [c9r8333targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 1 _ (by rfl)
  have c9r8334_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r8334targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,3),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,3),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,3),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(0,6),(1,4),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r8334choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8334targets [(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)] c9r8334choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8334targets, c9r8334choice, ?_, checked⟩
    intro S h
    simp only [c9r8334targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 11 _ (by rfl)
  have c9r8335_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r8335targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(0,5),(0,6),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r8335choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8335targets [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r8335choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8335targets, c9r8335choice, ?_, checked⟩
    intro S h
    simp only [c9r8335targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8328_closed
  · subst row; exact c9r8329_closed
  · subst row; exact c9r8330_closed
  · subst row; exact c9r8331_closed
  · subst row; exact c9r8332_closed
  · subst row; exact c9r8333_closed
  · subst row; exact c9r8334_closed
  · subst row; exact c9r8335_closed
theorem C9R08320G2 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8336_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r8336targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,5),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(0,5),(0,6),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(0,5),(0,6),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r8336choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8336targets [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r8336choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8336targets, c9r8336choice, ?_, checked⟩
    intro S h
    simp only [c9r8336targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 24 _ (by rfl)
  have c9r8337_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r8337targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,4),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,5),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(0,5),(0,6),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r8337choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8337targets [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r8337choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8337targets, c9r8337choice, ?_, checked⟩
    intro S h
    simp only [c9r8337targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 27 _ (by rfl)
  have c9r8338_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r8338targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,4),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,5),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(0,5),(0,6),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r8338choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8338targets [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r8338choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8338targets, c9r8338choice, ?_, checked⟩
    intro S h
    simp only [c9r8338targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 29 _ (by rfl)
  have c9r8339_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r8339targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,4),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,5),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(0,5),(0,6),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r8339choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8339targets [(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r8339choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8339targets, c9r8339choice, ?_, checked⟩
    intro S h
    simp only [c9r8339targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 31 _ (by rfl)
  have c9r8340_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r8340targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,4),(1,3),(1,4),(1,5),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,5),(1,3),(1,4),(1,5),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(0,5),(0,6),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r8340choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8340targets [(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r8340choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8340targets, c9r8340choice, ?_, checked⟩
    intro S h
    simp only [c9r8340targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 7 _ (by rfl)
  have c9r8341_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r8341targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,4),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,5),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(0,5),(0,6),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r8341choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8341targets [(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r8341choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8341targets, c9r8341choice, ?_, checked⟩
    intro S h
    simp only [c9r8341targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 14 _ (by rfl)
  have c9r8342_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r8342targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,3),(1,4),(1,5),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,5),(1,3),(1,4),(1,5),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,4),(0,5),(0,6),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r8342choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8342targets [(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r8342choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8342targets, c9r8342choice, ?_, checked⟩
    intro S h
    simp only [c9r8342targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 22 _ (by rfl)
  have c9r8343_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r8343targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,3),(1,4),(1,5),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,3),(1,4),(1,5),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(0,6),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(0,5),(0,6),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r8343choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8343targets [(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r8343choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8343targets, c9r8343choice, ?_, checked⟩
    intro S h
    simp only [c9r8343targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8336_closed
  · subst row; exact c9r8337_closed
  · subst row; exact c9r8338_closed
  · subst row; exact c9r8339_closed
  · subst row; exact c9r8340_closed
  · subst row; exact c9r8341_closed
  · subst row; exact c9r8342_closed
  · subst row; exact c9r8343_closed
theorem C9R08320G3 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8344_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c9r8344targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c9r8344choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8344targets [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c9r8344choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8344targets, c9r8344choice, ?_, checked⟩
    intro S h
    simp only [c9r8344targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 14 _ (by rfl)
  have c9r8345_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] := by
    let c9r8345targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)]]
    let c9r8345choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8345targets [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] c9r8345choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8345targets, c9r8345choice, ?_, checked⟩
    intro S h
    simp only [c9r8345targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 20 _ (by rfl)
  have c9r8346_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] := by
    let c9r8346targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)]]
    let c9r8346choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8346targets [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] c9r8346choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8346targets, c9r8346choice, ?_, checked⟩
    intro S h
    simp only [c9r8346targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 25 _ (by rfl)
  have c9r8347_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] := by
    let c9r8347targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)]]
    let c9r8347choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8347targets [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] c9r8347choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8347targets, c9r8347choice, ?_, checked⟩
    intro S h
    simp only [c9r8347targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 29 _ (by rfl)
  have c9r8348_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] := by
    let c9r8348targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)]]
    let c9r8348choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8348targets [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] c9r8348choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8348targets, c9r8348choice, ?_, checked⟩
    intro S h
    simp only [c9r8348targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 0 _ (by rfl)
  have c9r8349_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] := by
    let c9r8349targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)]]
    let c9r8349choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8349targets [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] c9r8349choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8349targets, c9r8349choice, ?_, checked⟩
    intro S h
    simp only [c9r8349targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 2 _ (by rfl)
  have c9r8350_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] := by
    let c9r8350targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)]]
    let c9r8350choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8350targets [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] c9r8350choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8350targets, c9r8350choice, ?_, checked⟩
    intro S h
    simp only [c9r8350targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 4 _ (by rfl)
  have c9r8351_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c9r8351targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c9r8351choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8351targets [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c9r8351choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8351targets, c9r8351choice, ?_, checked⟩
    intro S h
    simp only [c9r8351targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,true,true] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8344_closed
  · subst row; exact c9r8345_closed
  · subst row; exact c9r8346_closed
  · subst row; exact c9r8347_closed
  · subst row; exact c9r8348_closed
  · subst row; exact c9r8349_closed
  · subst row; exact c9r8350_closed
  · subst row; exact c9r8351_closed
theorem C9R08320_closed (row : List GridPoint) (h : FamilyMember row F9B004L4) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L4, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08320G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08320G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08320G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08320G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08320G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08320G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08320G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08320G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08320G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08320G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08320G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08320G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08320G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08320G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08320G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08320G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08320G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08320G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08320G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08320G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08320G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08320G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08320G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08320G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08320G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08320G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08320G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08320G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08320G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08320G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08320G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08320G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
