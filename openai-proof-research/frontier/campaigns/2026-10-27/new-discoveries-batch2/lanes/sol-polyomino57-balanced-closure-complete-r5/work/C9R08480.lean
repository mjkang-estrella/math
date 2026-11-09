import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08480G0 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8480_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r8480targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(0,5),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r8480choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8480targets [(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r8480choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8480targets, c9r8480choice, ?_, checked⟩
    intro S h
    simp only [c9r8480targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 28 _ (by rfl)
  have c9r8481_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r8481targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(0,5),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r8481choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8481targets [(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r8481choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8481targets, c9r8481choice, ?_, checked⟩
    intro S h
    simp only [c9r8481targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 3 _ (by rfl)
  have c9r8482_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r8482targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,4),(0,5),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(0,5),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r8482choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8482targets [(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r8482choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8482targets, c9r8482choice, ?_, checked⟩
    intro S h
    simp only [c9r8482targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 6 _ (by rfl)
  have c9r8483_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r8483targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,4),(0,5),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r8483choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8483targets [(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r8483choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8483targets, c9r8483choice, ?_, checked⟩
    intro S h
    simp only [c9r8483targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 8 _ (by rfl)
  have c9r8484_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r8484targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,4),(0,5),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r8484choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8484targets [(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r8484choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8484targets, c9r8484choice, ?_, checked⟩
    intro S h
    simp only [c9r8484targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 10 _ (by rfl)
  have c9r8485_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r8485targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,4),(0,5),(1,3),(1,4),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r8485choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8485targets [(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)] c9r8485choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8485targets, c9r8485choice, ?_, checked⟩
    intro S h
    simp only [c9r8485targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 15 _ (by rfl)
  have c9r8486_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r8486targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,4),(0,5),(1,3),(1,4),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r8486choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8486targets [(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)] c9r8486choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8486targets, c9r8486choice, ?_, checked⟩
    intro S h
    simp only [c9r8486targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 21 _ (by rfl)
  have c9r8487_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r8487targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,4),(0,5),(1,3),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r8487choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8487targets [(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r8487choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8487targets, c9r8487choice, ?_, checked⟩
    intro S h
    simp only [c9r8487targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8480_closed
  · subst row; exact c9r8481_closed
  · subst row; exact c9r8482_closed
  · subst row; exact c9r8483_closed
  · subst row; exact c9r8484_closed
  · subst row; exact c9r8485_closed
  · subst row; exact c9r8486_closed
  · subst row; exact c9r8487_closed
theorem C9R08480G1 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8488_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r8488targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r8488choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8488targets [(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r8488choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8488targets, c9r8488choice, ?_, checked⟩
    intro S h
    simp only [c9r8488targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 7 _ (by rfl)
  have c9r8489_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r8489targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r8489choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8489targets [(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)] c9r8489choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8489targets, c9r8489choice, ?_, checked⟩
    intro S h
    simp only [c9r8489targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 16 _ (by rfl)
  have c9r8490_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r8490targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r8490choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8490targets [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r8490choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8490targets, c9r8490choice, ?_, checked⟩
    intro S h
    simp only [c9r8490targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 25 _ (by rfl)
  have c9r8491_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r8491targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(0,5),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r8491choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8491targets [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r8491choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8491targets, c9r8491choice, ?_, checked⟩
    intro S h
    simp only [c9r8491targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 29 _ (by rfl)
  have c9r8492_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r8492targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,4),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r8492choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8492targets [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r8492choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8492targets, c9r8492choice, ?_, checked⟩
    intro S h
    simp only [c9r8492targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 0 _ (by rfl)
  have c9r8493_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r8493targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,4),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r8493choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8493targets [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r8493choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8493targets, c9r8493choice, ?_, checked⟩
    intro S h
    simp only [c9r8493targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 2 _ (by rfl)
  have c9r8494_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r8494targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,4),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r8494choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8494targets [(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r8494choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8494targets, c9r8494choice, ?_, checked⟩
    intro S h
    simp only [c9r8494targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 4 _ (by rfl)
  have c9r8495_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r8495targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(0,5),(1,4),(1,5),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r8495choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8495targets [(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r8495choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8495targets, c9r8495choice, ?_, checked⟩
    intro S h
    simp only [c9r8495targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8488_closed
  · subst row; exact c9r8489_closed
  · subst row; exact c9r8490_closed
  · subst row; exact c9r8491_closed
  · subst row; exact c9r8492_closed
  · subst row; exact c9r8493_closed
  · subst row; exact c9r8494_closed
  · subst row; exact c9r8495_closed
theorem C9R08480G2 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8496_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r8496targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,4),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(0,5),(1,4),(1,5),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r8496choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8496targets [(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r8496choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8496targets, c9r8496choice, ?_, checked⟩
    intro S h
    simp only [c9r8496targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 19 _ (by rfl)
  have c9r8497_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r8497targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,3),(1,4),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,4),(0,5),(1,4),(1,5),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r8497choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8497targets [(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r8497choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8497targets, c9r8497choice, ?_, checked⟩
    intro S h
    simp only [c9r8497targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 27 _ (by rfl)
  have c9r8498_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r8498targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r8498choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8498targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r8498choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8498targets, c9r8498choice, ?_, checked⟩
    intro S h
    simp only [c9r8498targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 7 _ (by rfl)
  have c9r8499_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] := by
    let c9r8499targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,4),(0,5),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c9r8499choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8499targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] c9r8499choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8499targets, c9r8499choice, ?_, checked⟩
    intro S h
    simp only [c9r8499targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 12 _ (by rfl)
  have c9r8500_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r8500targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r8500choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8500targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r8500choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8500targets, c9r8500choice, ?_, checked⟩
    intro S h
    simp only [c9r8500targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 16 _ (by rfl)
  have c9r8501_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r8501targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r8501choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8501targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r8501choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8501targets, c9r8501choice, ?_, checked⟩
    intro S h
    simp only [c9r8501targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 19 _ (by rfl)
  have c9r8502_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r8502targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r8502choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8502targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r8502choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8502targets, c9r8502choice, ?_, checked⟩
    intro S h
    simp only [c9r8502targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 21 _ (by rfl)
  have c9r8503_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r8503targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r8503choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8503targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r8503choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8503targets, c9r8503choice, ?_, checked⟩
    intro S h
    simp only [c9r8503targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8496_closed
  · subst row; exact c9r8497_closed
  · subst row; exact c9r8498_closed
  · subst row; exact c9r8499_closed
  · subst row; exact c9r8500_closed
  · subst row; exact c9r8501_closed
  · subst row; exact c9r8502_closed
  · subst row; exact c9r8503_closed
theorem C9R08480G3 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8504_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r8504targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(0,5),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r8504choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8504targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r8504choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8504targets, c9r8504choice, ?_, checked⟩
    intro S h
    simp only [c9r8504targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 27 _ (by rfl)
  have c9r8505_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] := by
    let c9r8505targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,4),(0,5),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)]]
    let c9r8505choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8505targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] c9r8505choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8505targets, c9r8505choice, ?_, checked⟩
    intro S h
    simp only [c9r8505targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 30 _ (by rfl)
  have c9r8506_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] := by
    let c9r8506targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,4),(0,5),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)]]
    let c9r8506choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8506targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] c9r8506choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8506targets, c9r8506choice, ?_, checked⟩
    intro S h
    simp only [c9r8506targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 1 _ (by rfl)
  have c9r8507_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] := by
    let c9r8507targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,4),(0,5),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,4),(0,5),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)]]
    let c9r8507choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8507targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] c9r8507choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8507targets, c9r8507choice, ?_, checked⟩
    intro S h
    simp only [c9r8507targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 3 _ (by rfl)
  have c9r8508_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)] := by
    let c9r8508targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c9r8508choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8508targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)] c9r8508choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8508targets, c9r8508choice, ?_, checked⟩
    intro S h
    simp only [c9r8508targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 6 _ (by rfl)
  have c9r8509_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)] := by
    let c9r8509targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)]]
    let c9r8509choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8509targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)] c9r8509choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8509targets, c9r8509choice, ?_, checked⟩
    intro S h
    simp only [c9r8509targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 9 _ (by rfl)
  have c9r8510_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)] := by
    let c9r8510targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)]]
    let c9r8510choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8510targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)] c9r8510choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8510targets, c9r8510choice, ?_, checked⟩
    intro S h
    simp only [c9r8510targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 12 _ (by rfl)
  have c9r8511_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)] := by
    let c9r8511targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c9r8511choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8511targets [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)] c9r8511choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8511targets, c9r8511choice, ?_, checked⟩
    intro S h
    simp only [c9r8511targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,true,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8504_closed
  · subst row; exact c9r8505_closed
  · subst row; exact c9r8506_closed
  · subst row; exact c9r8507_closed
  · subst row; exact c9r8508_closed
  · subst row; exact c9r8509_closed
  · subst row; exact c9r8510_closed
  · subst row; exact c9r8511_closed
theorem C9R08480_closed (row : List GridPoint) (h : FamilyMember row F9B004L9) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L9, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08480G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08480G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08480G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08480G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08480G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08480G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08480G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08480G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08480G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08480G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08480G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08480G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08480G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08480G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08480G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08480G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08480G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08480G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08480G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08480G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08480G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08480G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08480G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08480G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08480G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08480G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08480G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08480G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08480G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08480G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08480G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08480G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
