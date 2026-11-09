import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R01472G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1472_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)] := by
    let c10r1472targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c10r1472choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1472targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)] c10r1472choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1472targets, c10r1472choice, ?_, checked⟩
    intro S h
    simp only [c10r1472targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
  have c10r1473_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)] := by
    let c10r1473targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c10r1473choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1473targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)] c10r1473choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1473targets, c10r1473choice, ?_, checked⟩
    intro S h
    simp only [c10r1473targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 19 _ (by rfl)
  have c10r1474_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)] := by
    let c10r1474targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c10r1474choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1474targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)] c10r1474choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1474targets, c10r1474choice, ?_, checked⟩
    intro S h
    simp only [c10r1474targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 22 _ (by rfl)
  have c10r1475_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)] := by
    let c10r1475targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c10r1475choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1475targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)] c10r1475choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1475targets, c10r1475choice, ?_, checked⟩
    intro S h
    simp only [c10r1475targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 24 _ (by rfl)
  have c10r1476_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)] := by
    let c10r1476targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c10r1476choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1476targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)] c10r1476choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1476targets, c10r1476choice, ?_, checked⟩
    intro S h
    simp only [c10r1476targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 28 _ (by rfl)
  have c10r1477_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)] := by
    let c10r1477targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c10r1477choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1477targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)] c10r1477choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1477targets, c10r1477choice, ?_, checked⟩
    intro S h
    simp only [c10r1477targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 31 _ (by rfl)
  have c10r1478_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)] := by
    let c10r1478targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c10r1478choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1478targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)] c10r1478choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1478targets, c10r1478choice, ?_, checked⟩
    intro S h
    simp only [c10r1478targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 2 _ (by rfl)
  have c10r1479_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7)] := by
    let c10r1479targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,7),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)]]
    let c10r1479choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1479targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7)] c10r1479choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1479targets, c10r1479choice, ?_, checked⟩
    intro S h
    simp only [c10r1479targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1472_closed
  · subst row; exact c10r1473_closed
  · subst row; exact c10r1474_closed
  · subst row; exact c10r1475_closed
  · subst row; exact c10r1476_closed
  · subst row; exact c10r1477_closed
  · subst row; exact c10r1478_closed
  · subst row; exact c10r1479_closed
theorem C10R01472G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1480_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1)] := by
    let c10r1480targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)]]
    let c10r1480choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1480targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1)] c10r1480choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1480targets, c10r1480choice, ?_, checked⟩
    intro S h
    simp only [c10r1480targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 16 _ (by rfl)
  have c10r1481_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3)] := by
    let c10r1481targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)]]
    let c10r1481choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1481targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3)] c10r1481choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1481targets, c10r1481choice, ?_, checked⟩
    intro S h
    simp only [c10r1481targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 21 _ (by rfl)
  have c10r1482_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4)] := by
    let c10r1482targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)]]
    let c10r1482choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1482targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4)] c10r1482choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1482targets, c10r1482choice, ?_, checked⟩
    intro S h
    simp only [c10r1482targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 24 _ (by rfl)
  have c10r1483_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5)] := by
    let c10r1483targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)]]
    let c10r1483choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1483targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5)] c10r1483choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1483targets, c10r1483choice, ?_, checked⟩
    intro S h
    simp only [c10r1483targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 26 _ (by rfl)
  have c10r1484_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6)] := by
    let c10r1484targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)]]
    let c10r1484choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1484targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6)] c10r1484choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1484targets, c10r1484choice, ?_, checked⟩
    intro S h
    simp only [c10r1484targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 28 _ (by rfl)
  have c10r1485_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)] := by
    let c10r1485targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)]]
    let c10r1485choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1485targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)] c10r1485choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1485targets, c10r1485choice, ?_, checked⟩
    intro S h
    simp only [c10r1485targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 2 _ (by rfl)
  have c10r1486_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2)] := by
    let c10r1486targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)]]
    let c10r1486choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1486targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2)] c10r1486choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1486targets, c10r1486choice, ?_, checked⟩
    intro S h
    simp only [c10r1486targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 7 _ (by rfl)
  have c10r1487_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3)] := by
    let c10r1487targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(3,3)]]
    let c10r1487choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1487targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3)] c10r1487choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1487targets, c10r1487choice, ?_, checked⟩
    intro S h
    simp only [c10r1487targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1480_closed
  · subst row; exact c10r1481_closed
  · subst row; exact c10r1482_closed
  · subst row; exact c10r1483_closed
  · subst row; exact c10r1484_closed
  · subst row; exact c10r1485_closed
  · subst row; exact c10r1486_closed
  · subst row; exact c10r1487_closed
theorem C10R01472G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1488_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4)] := by
    let c10r1488targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4),(3,4)]]
    let c10r1488choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1488targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4)] c10r1488choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1488targets, c10r1488choice, ?_, checked⟩
    intro S h
    simp only [c10r1488targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 14 _ (by rfl)
  have c10r1489_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5)] := by
    let c10r1489targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5),(3,5)]]
    let c10r1489choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1489targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5)] c10r1489choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1489targets, c10r1489choice, ?_, checked⟩
    intro S h
    simp only [c10r1489targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 17 _ (by rfl)
  have c10r1490_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1)] := by
    let c10r1490targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1),(4,1)]]
    let c10r1490choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1490targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1)] c10r1490choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1490targets, c10r1490choice, ?_, checked⟩
    intro S h
    simp only [c10r1490targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 20 _ (by rfl)
  have c10r1491_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3)] := by
    let c10r1491targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)]]
    let c10r1491choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1491targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3)] c10r1491choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1491targets, c10r1491choice, ?_, checked⟩
    intro S h
    simp only [c10r1491targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 24 _ (by rfl)
  have c10r1492_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4)] := by
    let c10r1492targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)]]
    let c10r1492choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1492targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4)] c10r1492choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1492targets, c10r1492choice, ?_, checked⟩
    intro S h
    simp only [c10r1492targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 27 _ (by rfl)
  have c10r1493_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5)] := by
    let c10r1493targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)]]
    let c10r1493choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1493targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5)] c10r1493choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1493targets, c10r1493choice, ?_, checked⟩
    intro S h
    simp only [c10r1493targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 30 _ (by rfl)
  have c10r1494_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3)] := by
    let c10r1494targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)]]
    let c10r1494choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1494targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3)] c10r1494choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1494targets, c10r1494choice, ?_, checked⟩
    intro S h
    simp only [c10r1494targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 1 _ (by rfl)
  have c10r1495_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5)] := by
    let c10r1495targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)]]
    let c10r1495choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1495targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5)] c10r1495choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1495targets, c10r1495choice, ?_, checked⟩
    intro S h
    simp only [c10r1495targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1488_closed
  · subst row; exact c10r1489_closed
  · subst row; exact c10r1490_closed
  · subst row; exact c10r1491_closed
  · subst row; exact c10r1492_closed
  · subst row; exact c10r1493_closed
  · subst row; exact c10r1494_closed
  · subst row; exact c10r1495_closed
theorem C10R01472G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1496_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4)] := by
    let c10r1496targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4)]]
    let c10r1496choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1496targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4)] c10r1496choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1496targets, c10r1496choice, ?_, checked⟩
    intro S h
    simp only [c10r1496targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 7 _ (by rfl)
  have c10r1497_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6)] := by
    let c10r1497targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6),(3,6)]]
    let c10r1497choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1497targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6)] c10r1497choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1497targets, c10r1497choice, ?_, checked⟩
    intro S h
    simp only [c10r1497targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 10 _ (by rfl)
  have c10r1498_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5)] := by
    let c10r1498targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5),(4,5)]]
    let c10r1498choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1498targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5)] c10r1498choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1498targets, c10r1498choice, ?_, checked⟩
    intro S h
    simp only [c10r1498targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 13 _ (by rfl)
  have c10r1499_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c10r1499targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c10r1499choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1499targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2)] c10r1499choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1499targets, c10r1499choice, ?_, checked⟩
    intro S h
    simp only [c10r1499targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 19 _ (by rfl)
  have c10r1500_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3)] := by
    let c10r1500targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)]]
    let c10r1500choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1500targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3)] c10r1500choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1500targets, c10r1500choice, ?_, checked⟩
    intro S h
    simp only [c10r1500targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 23 _ (by rfl)
  have c10r1501_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4)] := by
    let c10r1501targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)]]
    let c10r1501choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1501targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4)] c10r1501choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1501targets, c10r1501choice, ?_, checked⟩
    intro S h
    simp only [c10r1501targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 27 _ (by rfl)
  have c10r1502_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0)] := by
    let c10r1502targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c10r1502choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1502targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0)] c10r1502choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1502targets, c10r1502choice, ?_, checked⟩
    intro S h
    simp only [c10r1502targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 29 _ (by rfl)
  have c10r1503_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c10r1503targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c10r1503choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1503targets [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1)] c10r1503choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1503targets, c10r1503choice, ?_, checked⟩
    intro S h
    simp only [c10r1503targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1496_closed
  · subst row; exact c10r1497_closed
  · subst row; exact c10r1498_closed
  · subst row; exact c10r1499_closed
  · subst row; exact c10r1500_closed
  · subst row; exact c10r1501_closed
  · subst row; exact c10r1502_closed
  · subst row; exact c10r1503_closed
theorem C10R01472_closed (row : List GridPoint) (h : FamilyMember row F10B000L46) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L46, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R01472G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01472G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01472G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01472G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01472G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01472G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01472G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01472G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01472G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01472G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01472G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01472G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01472G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01472G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01472G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01472G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01472G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01472G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01472G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01472G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01472G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01472G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01472G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01472G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01472G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01472G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01472G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01472G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01472G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01472G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01472G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01472G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
