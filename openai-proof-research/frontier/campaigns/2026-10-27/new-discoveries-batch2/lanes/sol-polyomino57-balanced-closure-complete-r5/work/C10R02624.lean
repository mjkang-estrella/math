import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R02624G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2624_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] := by
    let c10r2624targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c10r2624choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2624targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] c10r2624choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2624targets, c10r2624choice, ?_, checked⟩
    intro S h
    simp only [c10r2624targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 24 _ (by rfl)
  have c10r2625_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)] := by
    let c10r2625targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c10r2625choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2625targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)] c10r2625choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2625targets, c10r2625choice, ?_, checked⟩
    intro S h
    simp only [c10r2625targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 28 _ (by rfl)
  have c10r2626_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)] := by
    let c10r2626targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c10r2626choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2626targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)] c10r2626choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2626targets, c10r2626choice, ?_, checked⟩
    intro S h
    simp only [c10r2626targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 31 _ (by rfl)
  have c10r2627_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)] := by
    let c10r2627targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c10r2627choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2627targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)] c10r2627choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2627targets, c10r2627choice, ?_, checked⟩
    intro S h
    simp only [c10r2627targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 1 _ (by rfl)
  have c10r2628_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)] := by
    let c10r2628targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c10r2628choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2628targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)] c10r2628choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2628targets, c10r2628choice, ?_, checked⟩
    intro S h
    simp only [c10r2628targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 5 _ (by rfl)
  have c10r2629_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)] := by
    let c10r2629targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c10r2629choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2629targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)] c10r2629choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2629targets, c10r2629choice, ?_, checked⟩
    intro S h
    simp only [c10r2629targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 8 _ (by rfl)
  have c10r2630_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)] := by
    let c10r2630targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c10r2630choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2630targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)] c10r2630choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2630targets, c10r2630choice, ?_, checked⟩
    intro S h
    simp only [c10r2630targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 10 _ (by rfl)
  have c10r2631_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)] := by
    let c10r2631targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c10r2631choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2631targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)] c10r2631choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2631targets, c10r2631choice, ?_, checked⟩
    intro S h
    simp only [c10r2631targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2624_closed
  · subst row; exact c10r2625_closed
  · subst row; exact c10r2626_closed
  · subst row; exact c10r2627_closed
  · subst row; exact c10r2628_closed
  · subst row; exact c10r2629_closed
  · subst row; exact c10r2630_closed
  · subst row; exact c10r2631_closed
theorem C10R02624G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2632_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)] := by
    let c10r2632targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c10r2632choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2632targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)] c10r2632choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2632targets, c10r2632choice, ?_, checked⟩
    intro S h
    simp only [c10r2632targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 17 _ (by rfl)
  have c10r2633_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)] := by
    let c10r2633targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c10r2633choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r2633targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)] c10r2633choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2633targets, c10r2633choice, ?_, checked⟩
    intro S h
    simp only [c10r2633targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 20 _ (by rfl)
  have c10r2634_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)] := by
    let c10r2634targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c10r2634choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2634targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)] c10r2634choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2634targets, c10r2634choice, ?_, checked⟩
    intro S h
    simp only [c10r2634targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 25 _ (by rfl)
  have c10r2635_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)] := by
    let c10r2635targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c10r2635choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2635targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)] c10r2635choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2635targets, c10r2635choice, ?_, checked⟩
    intro S h
    simp only [c10r2635targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 29 _ (by rfl)
  have c10r2636_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)] := by
    let c10r2636targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c10r2636choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2636targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)] c10r2636choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2636targets, c10r2636choice, ?_, checked⟩
    intro S h
    simp only [c10r2636targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 31 _ (by rfl)
  have c10r2637_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)] := by
    let c10r2637targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c10r2637choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2637targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)] c10r2637choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2637targets, c10r2637choice, ?_, checked⟩
    intro S h
    simp only [c10r2637targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 1 _ (by rfl)
  have c10r2638_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)] := by
    let c10r2638targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3)]]
    let c10r2638choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2638targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)] c10r2638choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2638targets, c10r2638choice, ?_, checked⟩
    intro S h
    simp only [c10r2638targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 5 _ (by rfl)
  have c10r2639_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)] := by
    let c10r2639targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4)]]
    let c10r2639choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2639targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)] c10r2639choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2639targets, c10r2639choice, ?_, checked⟩
    intro S h
    simp only [c10r2639targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2632_closed
  · subst row; exact c10r2633_closed
  · subst row; exact c10r2634_closed
  · subst row; exact c10r2635_closed
  · subst row; exact c10r2636_closed
  · subst row; exact c10r2637_closed
  · subst row; exact c10r2638_closed
  · subst row; exact c10r2639_closed
theorem C10R02624G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2640_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)] := by
    let c10r2640targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3)]]
    let c10r2640choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2640targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)] c10r2640choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2640targets, c10r2640choice, ?_, checked⟩
    intro S h
    simp only [c10r2640targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 11 _ (by rfl)
  have c10r2641_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)] := by
    let c10r2641targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5)]]
    let c10r2641choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2641targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)] c10r2641choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2641targets, c10r2641choice, ?_, checked⟩
    intro S h
    simp only [c10r2641targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 14 _ (by rfl)
  have c10r2642_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)] := by
    let c10r2642targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4)]]
    let c10r2642choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2642targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)] c10r2642choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2642targets, c10r2642choice, ?_, checked⟩
    intro S h
    simp only [c10r2642targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 17 _ (by rfl)
  have c10r2643_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)] := by
    let c10r2643targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c10r2643choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2643targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)] c10r2643choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2643targets, c10r2643choice, ?_, checked⟩
    intro S h
    simp only [c10r2643targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 23 _ (by rfl)
  have c10r2644_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)] := by
    let c10r2644targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4)]]
    let c10r2644choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2644targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)] c10r2644choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2644targets, c10r2644choice, ?_, checked⟩
    intro S h
    simp only [c10r2644targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 27 _ (by rfl)
  have c10r2645_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)] := by
    let c10r2645targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)]]
    let c10r2645choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2645targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)] c10r2645choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2645targets, c10r2645choice, ?_, checked⟩
    intro S h
    simp only [c10r2645targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 30 _ (by rfl)
  have c10r2646_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)] := by
    let c10r2646targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)]]
    let c10r2646choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2646targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)] c10r2646choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2646targets, c10r2646choice, ?_, checked⟩
    intro S h
    simp only [c10r2646targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 0 _ (by rfl)
  have c10r2647_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)] := by
    let c10r2647targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)]]
    let c10r2647choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2647targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)] c10r2647choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2647targets, c10r2647choice, ?_, checked⟩
    intro S h
    simp only [c10r2647targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2640_closed
  · subst row; exact c10r2641_closed
  · subst row; exact c10r2642_closed
  · subst row; exact c10r2643_closed
  · subst row; exact c10r2644_closed
  · subst row; exact c10r2645_closed
  · subst row; exact c10r2646_closed
  · subst row; exact c10r2647_closed
theorem C10R02624G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2648_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)] := by
    let c10r2648targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)]]
    let c10r2648choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2648targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)] c10r2648choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2648targets, c10r2648choice, ?_, checked⟩
    intro S h
    simp only [c10r2648targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 7 _ (by rfl)
  have c10r2649_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)] := by
    let c10r2649targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)]]
    let c10r2649choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2649targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)] c10r2649choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2649targets, c10r2649choice, ?_, checked⟩
    intro S h
    simp only [c10r2649targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 9 _ (by rfl)
  have c10r2650_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)] := by
    let c10r2650targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)]]
    let c10r2650choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2650targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)] c10r2650choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2650targets, c10r2650choice, ?_, checked⟩
    intro S h
    simp only [c10r2650targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 13 _ (by rfl)
  have c10r2651_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)] := by
    let c10r2651targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)]]
    let c10r2651choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2651targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)] c10r2651choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2651targets, c10r2651choice, ?_, checked⟩
    intro S h
    simp only [c10r2651targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 16 _ (by rfl)
  have c10r2652_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)] := by
    let c10r2652targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3)]]
    let c10r2652choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r2652targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)] c10r2652choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2652targets, c10r2652choice, ?_, checked⟩
    intro S h
    simp only [c10r2652targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 19 _ (by rfl)
  have c10r2653_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)] := by
    let c10r2653targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,5),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4),(3,4)]]
    let c10r2653choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2653targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)] c10r2653choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2653targets, c10r2653choice, ?_, checked⟩
    intro S h
    simp only [c10r2653targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 26 _ (by rfl)
  have c10r2654_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)] := by
    let c10r2654targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(3,0),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(3,0),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(3,0),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,5),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,5),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,5),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(3,4)]]
    let c10r2654choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2654targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)] c10r2654choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2654targets, c10r2654choice, ?_, checked⟩
    intro S h
    simp only [c10r2654targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,true] 0 _ (by rfl)
  have c10r2655_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)] := by
    let c10r2655targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c10r2655choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2655targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)] c10r2655choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2655targets, c10r2655choice, ?_, checked⟩
    intro S h
    simp only [c10r2655targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,true,true,true,true,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2648_closed
  · subst row; exact c10r2649_closed
  · subst row; exact c10r2650_closed
  · subst row; exact c10r2651_closed
  · subst row; exact c10r2652_closed
  · subst row; exact c10r2653_closed
  · subst row; exact c10r2654_closed
  · subst row; exact c10r2655_closed
theorem C10R02624_closed (row : List GridPoint) (h : FamilyMember row F10B001L18) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B001L18, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R02624G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02624G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02624G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02624G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02624G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02624G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02624G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02624G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02624G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02624G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02624G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02624G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02624G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02624G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02624G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02624G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02624G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02624G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02624G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02624G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02624G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02624G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02624G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02624G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02624G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02624G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02624G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02624G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02624G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02624G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02624G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02624G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
