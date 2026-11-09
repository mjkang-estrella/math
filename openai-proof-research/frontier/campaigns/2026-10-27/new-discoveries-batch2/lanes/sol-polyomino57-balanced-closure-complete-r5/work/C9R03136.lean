import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03136G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3136_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r3136targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r3136choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3136targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)] c9r3136choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3136targets, c9r3136choice, ?_, checked⟩
    intro S h
    simp only [c9r3136targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 0 _ (by rfl)
  have c9r3137_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r3137targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r3137choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3137targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r3137choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3137targets, c9r3137choice, ?_, checked⟩
    intro S h
    simp only [c9r3137targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 2 _ (by rfl)
  have c9r3138_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r3138targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r3138choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3138targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r3138choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3138targets, c9r3138choice, ?_, checked⟩
    intro S h
    simp only [c9r3138targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 4 _ (by rfl)
  have c9r3139_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r3139targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r3139choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3139targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)] c9r3139choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3139targets, c9r3139choice, ?_, checked⟩
    intro S h
    simp only [c9r3139targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 8 _ (by rfl)
  have c9r3140_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r3140targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r3140choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3140targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)] c9r3140choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3140targets, c9r3140choice, ?_, checked⟩
    intro S h
    simp only [c9r3140targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 11 _ (by rfl)
  have c9r3141_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r3141targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r3141choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3141targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)] c9r3141choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3141targets, c9r3141choice, ?_, checked⟩
    intro S h
    simp only [c9r3141targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 13 _ (by rfl)
  have c9r3142_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r3142targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r3142choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3142targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)] c9r3142choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3142targets, c9r3142choice, ?_, checked⟩
    intro S h
    simp only [c9r3142targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 16 _ (by rfl)
  have c9r3143_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r3143targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r3143choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3143targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)] c9r3143choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3143targets, c9r3143choice, ?_, checked⟩
    intro S h
    simp only [c9r3143targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3136_closed
  · subst row; exact c9r3137_closed
  · subst row; exact c9r3138_closed
  · subst row; exact c9r3139_closed
  · subst row; exact c9r3140_closed
  · subst row; exact c9r3141_closed
  · subst row; exact c9r3142_closed
  · subst row; exact c9r3143_closed
theorem C9R03136G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3144_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r3144targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r3144choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3144targets [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] c9r3144choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3144targets, c9r3144choice, ?_, checked⟩
    intro S h
    simp only [c9r3144targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 22 _ (by rfl)
  have c9r3145_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r3145targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r3145choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3145targets [(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r3145choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3145targets, c9r3145choice, ?_, checked⟩
    intro S h
    simp only [c9r3145targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 27 _ (by rfl)
  have c9r3146_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r3146targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r3146choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3146targets [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r3146choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3146targets, c9r3146choice, ?_, checked⟩
    intro S h
    simp only [c9r3146targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 0 _ (by rfl)
  have c9r3147_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r3147targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r3147choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3147targets [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r3147choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3147targets, c9r3147choice, ?_, checked⟩
    intro S h
    simp only [c9r3147targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 3 _ (by rfl)
  have c9r3148_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r3148targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r3148choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r3148targets [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r3148choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3148targets, c9r3148choice, ?_, checked⟩
    intro S h
    simp only [c9r3148targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 5 _ (by rfl)
  have c9r3149_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r3149targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r3149choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3149targets [(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r3149choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3149targets, c9r3149choice, ?_, checked⟩
    intro S h
    simp only [c9r3149targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 7 _ (by rfl)
  have c9r3150_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r3150targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r3150choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3150targets [(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r3150choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3150targets, c9r3150choice, ?_, checked⟩
    intro S h
    simp only [c9r3150targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 14 _ (by rfl)
  have c9r3151_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r3151targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3151choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3151targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r3151choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3151targets, c9r3151choice, ?_, checked⟩
    intro S h
    simp only [c9r3151targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3144_closed
  · subst row; exact c9r3145_closed
  · subst row; exact c9r3146_closed
  · subst row; exact c9r3147_closed
  · subst row; exact c9r3148_closed
  · subst row; exact c9r3149_closed
  · subst row; exact c9r3150_closed
  · subst row; exact c9r3151_closed
theorem C9R03136G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3152_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r3152targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r3152choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3152targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r3152choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3152targets, c9r3152choice, ?_, checked⟩
    intro S h
    simp only [c9r3152targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 25 _ (by rfl)
  have c9r3153_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r3153targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r3153choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3153targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r3153choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3153targets, c9r3153choice, ?_, checked⟩
    intro S h
    simp only [c9r3153targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 28 _ (by rfl)
  have c9r3154_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r3154targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r3154choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3154targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r3154choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3154targets, c9r3154choice, ?_, checked⟩
    intro S h
    simp only [c9r3154targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 30 _ (by rfl)
  have c9r3155_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r3155targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r3155choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3155targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r3155choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3155targets, c9r3155choice, ?_, checked⟩
    intro S h
    simp only [c9r3155targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 0 _ (by rfl)
  have c9r3156_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r3156targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r3156choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3156targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r3156choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3156targets, c9r3156choice, ?_, checked⟩
    intro S h
    simp only [c9r3156targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 3 _ (by rfl)
  have c9r3157_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r3157targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r3157choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3157targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r3157choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3157targets, c9r3157choice, ?_, checked⟩
    intro S h
    simp only [c9r3157targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 6 _ (by rfl)
  have c9r3158_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r3158targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r3158choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3158targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r3158choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3158targets, c9r3158choice, ?_, checked⟩
    intro S h
    simp only [c9r3158targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 8 _ (by rfl)
  have c9r3159_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r3159targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r3159choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3159targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r3159choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3159targets, c9r3159choice, ?_, checked⟩
    intro S h
    simp only [c9r3159targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3152_closed
  · subst row; exact c9r3153_closed
  · subst row; exact c9r3154_closed
  · subst row; exact c9r3155_closed
  · subst row; exact c9r3156_closed
  · subst row; exact c9r3157_closed
  · subst row; exact c9r3158_closed
  · subst row; exact c9r3159_closed
theorem C9R03136G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3160_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r3160targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r3160choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3160targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r3160choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3160targets, c9r3160choice, ?_, checked⟩
    intro S h
    simp only [c9r3160targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 14 _ (by rfl)
  have c9r3161_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r3161targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r3161choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3161targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r3161choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3161targets, c9r3161choice, ?_, checked⟩
    intro S h
    simp only [c9r3161targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 17 _ (by rfl)
  have c9r3162_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r3162targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r3162choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3162targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r3162choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3162targets, c9r3162choice, ?_, checked⟩
    intro S h
    simp only [c9r3162targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 20 _ (by rfl)
  have c9r3163_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r3163targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r3163choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3163targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)] c9r3163choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3163targets, c9r3163choice, ?_, checked⟩
    intro S h
    simp only [c9r3163targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 25 _ (by rfl)
  have c9r3164_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r3164targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r3164choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3164targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)] c9r3164choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3164targets, c9r3164choice, ?_, checked⟩
    intro S h
    simp only [c9r3164targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 27 _ (by rfl)
  have c9r3165_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r3165targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r3165choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3165targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)] c9r3165choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3165targets, c9r3165choice, ?_, checked⟩
    intro S h
    simp only [c9r3165targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 29 _ (by rfl)
  have c9r3166_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)] := by
    let c9r3166targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)]]
    let c9r3166choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3166targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)] c9r3166choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3166targets, c9r3166choice, ?_, checked⟩
    intro S h
    simp only [c9r3166targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 0 _ (by rfl)
  have c9r3167_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)] := by
    let c9r3167targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)]]
    let c9r3167choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3167targets [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)] c9r3167choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3167targets, c9r3167choice, ?_, checked⟩
    intro S h
    simp only [c9r3167targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3160_closed
  · subst row; exact c9r3161_closed
  · subst row; exact c9r3162_closed
  · subst row; exact c9r3163_closed
  · subst row; exact c9r3164_closed
  · subst row; exact c9r3165_closed
  · subst row; exact c9r3166_closed
  · subst row; exact c9r3167_closed
theorem C9R03136_closed (row : List GridPoint) (h : FamilyMember row F9B001L34) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L34, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03136G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03136G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03136G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03136G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03136G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03136G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03136G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03136G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03136G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03136G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03136G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03136G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03136G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03136G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03136G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03136G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03136G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03136G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03136G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03136G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03136G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03136G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03136G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03136G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03136G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03136G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03136G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03136G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03136G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03136G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03136G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03136G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
