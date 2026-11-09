import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08192G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8192_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r8192targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r8192choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8192targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r8192choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8192targets, c9r8192choice, ?_, checked⟩
    intro S h
    simp only [c9r8192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 27 _ (by rfl)
  have c9r8193_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)] := by
    let c9r8193targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,2)]]
    let c9r8193choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8193targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)] c9r8193choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8193targets, c9r8193choice, ?_, checked⟩
    intro S h
    simp only [c9r8193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 30 _ (by rfl)
  have c9r8194_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)] := by
    let c9r8194targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,3)]]
    let c9r8194choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8194targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)] c9r8194choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8194targets, c9r8194choice, ?_, checked⟩
    intro S h
    simp only [c9r8194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 1 _ (by rfl)
  have c9r8195_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)] := by
    let c9r8195targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(5,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(6,0)]]
    let c9r8195choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8195targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)] c9r8195choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8195targets, c9r8195choice, ?_, checked⟩
    intro S h
    simp only [c9r8195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 3 _ (by rfl)
  have c9r8196_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r8196targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r8196choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8196targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)] c9r8196choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8196targets, c9r8196choice, ?_, checked⟩
    intro S h
    simp only [c9r8196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 6 _ (by rfl)
  have c9r8197_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)] := by
    let c9r8197targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)]]
    let c9r8197choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8197targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)] c9r8197choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8197targets, c9r8197choice, ?_, checked⟩
    intro S h
    simp only [c9r8197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 9 _ (by rfl)
  have c9r8198_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)] := by
    let c9r8198targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)]]
    let c9r8198choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8198targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)] c9r8198choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8198targets, c9r8198choice, ?_, checked⟩
    intro S h
    simp only [c9r8198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 12 _ (by rfl)
  have c9r8199_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)] := by
    let c9r8199targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)]]
    let c9r8199choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8199targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)] c9r8199choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8199targets, c9r8199choice, ?_, checked⟩
    intro S h
    simp only [c9r8199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8192_closed
  · subst row; exact c9r8193_closed
  · subst row; exact c9r8194_closed
  · subst row; exact c9r8195_closed
  · subst row; exact c9r8196_closed
  · subst row; exact c9r8197_closed
  · subst row; exact c9r8198_closed
  · subst row; exact c9r8199_closed
theorem C9R08192G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8200_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)] := by
    let c9r8200targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)]]
    let c9r8200choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8200targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)] c9r8200choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8200targets, c9r8200choice, ?_, checked⟩
    intro S h
    simp only [c9r8200targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 18 _ (by rfl)
  have c9r8201_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)] := by
    let c9r8201targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,4)]]
    let c9r8201choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8201targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)] c9r8201choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8201targets, c9r8201choice, ?_, checked⟩
    intro S h
    simp only [c9r8201targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 21 _ (by rfl)
  have c9r8202_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)] := by
    let c9r8202targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3),(6,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3),(6,3)]]
    let c9r8202choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8202targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)] c9r8202choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8202targets, c9r8202choice, ?_, checked⟩
    intro S h
    simp only [c9r8202targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 24 _ (by rfl)
  have c9r8203_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r8203targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r8203choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8203targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)] c9r8203choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8203targets, c9r8203choice, ?_, checked⟩
    intro S h
    simp only [c9r8203targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 29 _ (by rfl)
  have c9r8204_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c9r8204targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c9r8204choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8204targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)] c9r8204choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8204targets, c9r8204choice, ?_, checked⟩
    intro S h
    simp only [c9r8204targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 31 _ (by rfl)
  have c9r8205_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c9r8205targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c9r8205choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8205targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)] c9r8205choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8205targets, c9r8205choice, ?_, checked⟩
    intro S h
    simp only [c9r8205targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 1 _ (by rfl)
  have c9r8206_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)] := by
    let c9r8206targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,3)]]
    let c9r8206choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8206targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)] c9r8206choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8206targets, c9r8206choice, ?_, checked⟩
    intro S h
    simp only [c9r8206targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 5 _ (by rfl)
  have c9r8207_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)] := by
    let c9r8207targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(6,0)]]
    let c9r8207choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8207targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)] c9r8207choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8207targets, c9r8207choice, ?_, checked⟩
    intro S h
    simp only [c9r8207targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8200_closed
  · subst row; exact c9r8201_closed
  · subst row; exact c9r8202_closed
  · subst row; exact c9r8203_closed
  · subst row; exact c9r8204_closed
  · subst row; exact c9r8205_closed
  · subst row; exact c9r8206_closed
  · subst row; exact c9r8207_closed
theorem C9R08192G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8208_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)] := by
    let c9r8208targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,2)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2),(6,2)]]
    let c9r8208choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8208targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)] c9r8208choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8208targets, c9r8208choice, ?_, checked⟩
    intro S h
    simp only [c9r8208targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 11 _ (by rfl)
  have c9r8209_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)] := by
    let c9r8209targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,1)]]
    let c9r8209choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8209targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)] c9r8209choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8209targets, c9r8209choice, ?_, checked⟩
    intro S h
    simp only [c9r8209targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 14 _ (by rfl)
  have c9r8210_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)] := by
    let c9r8210targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0),(7,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0),(6,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(6,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0),(7,0)]]
    let c9r8210choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8210targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)] c9r8210choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8210targets, c9r8210choice, ?_, checked⟩
    intro S h
    simp only [c9r8210targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 16 _ (by rfl)
  have c9r8211_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)] := by
    let c9r8211targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)]]
    let c9r8211choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8211targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)] c9r8211choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8211targets, c9r8211choice, ?_, checked⟩
    intro S h
    simp only [c9r8211targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 20 _ (by rfl)
  have c9r8212_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)] := by
    let c9r8212targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)]]
    let c9r8212choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8212targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)] c9r8212choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8212targets, c9r8212choice, ?_, checked⟩
    intro S h
    simp only [c9r8212targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 23 _ (by rfl)
  have c9r8213_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)] := by
    let c9r8213targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)]]
    let c9r8213choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8213targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)] c9r8213choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8213targets, c9r8213choice, ?_, checked⟩
    intro S h
    simp only [c9r8213targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 25 _ (by rfl)
  have c9r8214_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)] := by
    let c9r8214targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)]]
    let c9r8214choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8214targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)] c9r8214choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8214targets, c9r8214choice, ?_, checked⟩
    intro S h
    simp only [c9r8214targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 28 _ (by rfl)
  have c9r8215_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)] := by
    let c9r8215targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)]]
    let c9r8215choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8215targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)] c9r8215choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8215targets, c9r8215choice, ?_, checked⟩
    intro S h
    simp only [c9r8215targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8208_closed
  · subst row; exact c9r8209_closed
  · subst row; exact c9r8210_closed
  · subst row; exact c9r8211_closed
  · subst row; exact c9r8212_closed
  · subst row; exact c9r8213_closed
  · subst row; exact c9r8214_closed
  · subst row; exact c9r8215_closed
theorem C9R08192G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8216_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)] := by
    let c9r8216targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)]]
    let c9r8216choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8216targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)] c9r8216choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8216targets, c9r8216choice, ?_, checked⟩
    intro S h
    simp only [c9r8216targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 2 _ (by rfl)
  have c9r8217_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)] := by
    let c9r8217targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)]]
    let c9r8217choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8217targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)] c9r8217choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8217targets, c9r8217choice, ?_, checked⟩
    intro S h
    simp only [c9r8217targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 6 _ (by rfl)
  have c9r8218_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)] := by
    let c9r8218targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)]]
    let c9r8218choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8218targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)] c9r8218choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8218targets, c9r8218choice, ?_, checked⟩
    intro S h
    simp only [c9r8218targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 9 _ (by rfl)
  have c9r8219_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)] := by
    let c9r8219targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(6,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3),(6,3)]]
    let c9r8219choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8219targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)] c9r8219choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8219targets, c9r8219choice, ?_, checked⟩
    intro S h
    simp only [c9r8219targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 11 _ (by rfl)
  have c9r8220_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)] := by
    let c9r8220targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)]]
    let c9r8220choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8220targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)] c9r8220choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8220targets, c9r8220choice, ?_, checked⟩
    intro S h
    simp only [c9r8220targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 15 _ (by rfl)
  have c9r8221_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)] := by
    let c9r8221targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,3)]]
    let c9r8221choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8221targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)] c9r8221choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8221targets, c9r8221choice, ?_, checked⟩
    intro S h
    simp only [c9r8221targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 18 _ (by rfl)
  have c9r8222_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)] := by
    let c9r8222targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2),(7,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2),(7,2)]]
    let c9r8222choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8222targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)] c9r8222choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8222targets, c9r8222choice, ?_, checked⟩
    intro S h
    simp only [c9r8222targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 21 _ (by rfl)
  have c9r8223_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r8223targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,1),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r8223choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8223targets [(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r8223choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8223targets, c9r8223choice, ?_, checked⟩
    intro S h
    simp only [c9r8223targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8216_closed
  · subst row; exact c9r8217_closed
  · subst row; exact c9r8218_closed
  · subst row; exact c9r8219_closed
  · subst row; exact c9r8220_closed
  · subst row; exact c9r8221_closed
  · subst row; exact c9r8222_closed
  · subst row; exact c9r8223_closed
theorem C9R08192_closed (row : List GridPoint) (h : FamilyMember row F9B004L0) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L0, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08192G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08192G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08192G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08192G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08192G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08192G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08192G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08192G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08192G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08192G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08192G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08192G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08192G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08192G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08192G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08192G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08192G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08192G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08192G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08192G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08192G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08192G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08192G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08192G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08192G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08192G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08192G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08192G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08192G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08192G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08192G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08192G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
