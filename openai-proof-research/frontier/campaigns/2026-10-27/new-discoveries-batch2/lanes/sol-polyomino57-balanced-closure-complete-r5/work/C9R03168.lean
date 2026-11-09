import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03168G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3168_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r3168targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r3168choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3168targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)] c9r3168choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3168targets, c9r3168choice, ?_, checked⟩
    intro S h
    simp only [c9r3168targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 6 _ (by rfl)
  have c9r3169_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r3169targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r3169choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3169targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)] c9r3169choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3169targets, c9r3169choice, ?_, checked⟩
    intro S h
    simp only [c9r3169targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 9 _ (by rfl)
  have c9r3170_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r3170targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r3170choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3170targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)] c9r3170choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3170targets, c9r3170choice, ?_, checked⟩
    intro S h
    simp only [c9r3170targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 11 _ (by rfl)
  have c9r3171_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r3171targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r3171choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3171targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)] c9r3171choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3171targets, c9r3171choice, ?_, checked⟩
    intro S h
    simp only [c9r3171targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 14 _ (by rfl)
  have c9r3172_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r3172targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r3172choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3172targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)] c9r3172choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3172targets, c9r3172choice, ?_, checked⟩
    intro S h
    simp only [c9r3172targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 17 _ (by rfl)
  have c9r3173_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r3173targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r3173choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3173targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)] c9r3173choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3173targets, c9r3173choice, ?_, checked⟩
    intro S h
    simp only [c9r3173targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 20 _ (by rfl)
  have c9r3174_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r3174targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r3174choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3174targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)] c9r3174choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3174targets, c9r3174choice, ?_, checked⟩
    intro S h
    simp only [c9r3174targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 25 _ (by rfl)
  have c9r3175_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r3175targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r3175choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3175targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)] c9r3175choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3175targets, c9r3175choice, ?_, checked⟩
    intro S h
    simp only [c9r3175targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3168_closed
  · subst row; exact c9r3169_closed
  · subst row; exact c9r3170_closed
  · subst row; exact c9r3171_closed
  · subst row; exact c9r3172_closed
  · subst row; exact c9r3173_closed
  · subst row; exact c9r3174_closed
  · subst row; exact c9r3175_closed
theorem C9R03168G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3176_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r3176targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r3176choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3176targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)] c9r3176choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3176targets, c9r3176choice, ?_, checked⟩
    intro S h
    simp only [c9r3176targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 2 _ (by rfl)
  have c9r3177_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r3177targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r3177choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3177targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)] c9r3177choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3177targets, c9r3177choice, ?_, checked⟩
    intro S h
    simp only [c9r3177targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 4 _ (by rfl)
  have c9r3178_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r3178targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r3178choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3178targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)] c9r3178choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3178targets, c9r3178choice, ?_, checked⟩
    intro S h
    simp only [c9r3178targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 6 _ (by rfl)
  have c9r3179_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)] := by
    let c9r3179targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)]]
    let c9r3179choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3179targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)] c9r3179choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3179targets, c9r3179choice, ?_, checked⟩
    intro S h
    simp only [c9r3179targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 9 _ (by rfl)
  have c9r3180_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)] := by
    let c9r3180targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0),(7,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0)]]
    let c9r3180choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3180targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)] c9r3180choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3180targets, c9r3180choice, ?_, checked⟩
    intro S h
    simp only [c9r3180targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 11 _ (by rfl)
  have c9r3181_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)] := by
    let c9r3181targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,2)]]
    let c9r3181choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3181targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)] c9r3181choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3181targets, c9r3181choice, ?_, checked⟩
    intro S h
    simp only [c9r3181targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 14 _ (by rfl)
  have c9r3182_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)] := by
    let c9r3182targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c9r3182choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3182targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)] c9r3182choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3182targets, c9r3182choice, ?_, checked⟩
    intro S h
    simp only [c9r3182targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 17 _ (by rfl)
  have c9r3183_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)] := by
    let c9r3183targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,2)]]
    let c9r3183choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3183targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)] c9r3183choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3183targets, c9r3183choice, ?_, checked⟩
    intro S h
    simp only [c9r3183targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3176_closed
  · subst row; exact c9r3177_closed
  · subst row; exact c9r3178_closed
  · subst row; exact c9r3179_closed
  · subst row; exact c9r3180_closed
  · subst row; exact c9r3181_closed
  · subst row; exact c9r3182_closed
  · subst row; exact c9r3183_closed
theorem C9R03168G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3184_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)] := by
    let c9r3184targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(7,0)]]
    let c9r3184choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3184targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)] c9r3184choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3184targets, c9r3184choice, ?_, checked⟩
    intro S h
    simp only [c9r3184targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 24 _ (by rfl)
  have c9r3185_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)] := by
    let c9r3185targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1),(7,1)]]
    let c9r3185choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3185targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)] c9r3185choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3185targets, c9r3185choice, ?_, checked⟩
    intro S h
    simp only [c9r3185targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 26 _ (by rfl)
  have c9r3186_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)] := by
    let c9r3186targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(7,0),(7,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(7,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(7,1)]]
    let c9r3186choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3186targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)] c9r3186choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3186targets, c9r3186choice, ?_, checked⟩
    intro S h
    simp only [c9r3186targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 29 _ (by rfl)
  have c9r3187_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)] := by
    let c9r3187targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(7,0),(8,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1),(7,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(7,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(8,0)]]
    let c9r3187choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < -1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3187targets [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)] c9r3187choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3187targets, c9r3187choice, ?_, checked⟩
    intro S h
    simp only [c9r3187targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 31 _ (by rfl)
  have c9r3188_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r3188targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r3188choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3188targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] c9r3188choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3188targets, c9r3188choice, ?_, checked⟩
    intro S h
    simp only [c9r3188targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 6 _ (by rfl)
  have c9r3189_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)] := by
    let c9r3189targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)]]
    let c9r3189choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3189targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)] c9r3189choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3189targets, c9r3189choice, ?_, checked⟩
    intro S h
    simp only [c9r3189targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 12 _ (by rfl)
  have c9r3190_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)] := by
    let c9r3190targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)]]
    let c9r3190choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3190targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)] c9r3190choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3190targets, c9r3190choice, ?_, checked⟩
    intro S h
    simp only [c9r3190targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 16 _ (by rfl)
  have c9r3191_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)] := by
    let c9r3191targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c9r3191choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3191targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)] c9r3191choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3191targets, c9r3191choice, ?_, checked⟩
    intro S h
    simp only [c9r3191targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3184_closed
  · subst row; exact c9r3185_closed
  · subst row; exact c9r3186_closed
  · subst row; exact c9r3187_closed
  · subst row; exact c9r3188_closed
  · subst row; exact c9r3189_closed
  · subst row; exact c9r3190_closed
  · subst row; exact c9r3191_closed
theorem C9R03168G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3192_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)] := by
    let c9r3192targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c9r3192choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3192targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)] c9r3192choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3192targets, c9r3192choice, ?_, checked⟩
    intro S h
    simp only [c9r3192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 21 _ (by rfl)
  have c9r3193_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r3193targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r3193choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3193targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] c9r3193choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3193targets, c9r3193choice, ?_, checked⟩
    intro S h
    simp only [c9r3193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 23 _ (by rfl)
  have c9r3194_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] := by
    let c9r3194targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)]]
    let c9r3194choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3194targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] c9r3194choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3194targets, c9r3194choice, ?_, checked⟩
    intro S h
    simp only [c9r3194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 28 _ (by rfl)
  have c9r3195_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)] := by
    let c9r3195targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)]]
    let c9r3195choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3195targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)] c9r3195choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3195targets, c9r3195choice, ?_, checked⟩
    intro S h
    simp only [c9r3195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 0 _ (by rfl)
  have c9r3196_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)] := by
    let c9r3196targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)]]
    let c9r3196choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3196targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)] c9r3196choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3196targets, c9r3196choice, ?_, checked⟩
    intro S h
    simp only [c9r3196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 3 _ (by rfl)
  have c9r3197_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)] := by
    let c9r3197targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,4)]]
    let c9r3197choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3197targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)] c9r3197choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3197targets, c9r3197choice, ?_, checked⟩
    intro S h
    simp only [c9r3197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 6 _ (by rfl)
  have c9r3198_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)] := by
    let c9r3198targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,1)]]
    let c9r3198choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3198targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)] c9r3198choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3198targets, c9r3198choice, ?_, checked⟩
    intro S h
    simp only [c9r3198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 9 _ (by rfl)
  have c9r3199_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)] := by
    let c9r3199targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)]]
    let c9r3199choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r3199targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)] c9r3199choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3199targets, c9r3199choice, ?_, checked⟩
    intro S h
    simp only [c9r3199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,false,false] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3192_closed
  · subst row; exact c9r3193_closed
  · subst row; exact c9r3194_closed
  · subst row; exact c9r3195_closed
  · subst row; exact c9r3196_closed
  · subst row; exact c9r3197_closed
  · subst row; exact c9r3198_closed
  · subst row; exact c9r3199_closed
theorem C9R03168_closed (row : List GridPoint) (h : FamilyMember row F9B001L35) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L35, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03168G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03168G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03168G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03168G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03168G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03168G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03168G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03168G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03168G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03168G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03168G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03168G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03168G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03168G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03168G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03168G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03168G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03168G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03168G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03168G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03168G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03168G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03168G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03168G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03168G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03168G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03168G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03168G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03168G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03168G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03168G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03168G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
