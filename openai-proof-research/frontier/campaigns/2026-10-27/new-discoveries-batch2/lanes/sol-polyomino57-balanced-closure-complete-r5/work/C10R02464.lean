import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R02464G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2464_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c10r2464targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c10r2464choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r2464targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)] c10r2464choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2464targets, c10r2464choice, ?_, checked⟩
    intro S h
    simp only [c10r2464targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 5 _ (by rfl)
  have c10r2465_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c10r2465targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c10r2465choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2465targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] c10r2465choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2465targets, c10r2465choice, ?_, checked⟩
    intro S h
    simp only [c10r2465targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 8 _ (by rfl)
  have c10r2466_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c10r2466targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c10r2466choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2466targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] c10r2466choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2466targets, c10r2466choice, ?_, checked⟩
    intro S h
    simp only [c10r2466targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 11 _ (by rfl)
  have c10r2467_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c10r2467targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c10r2467choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2467targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] c10r2467choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2467targets, c10r2467choice, ?_, checked⟩
    intro S h
    simp only [c10r2467targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 14 _ (by rfl)
  have c10r2468_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c10r2468targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c10r2468choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2468targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] c10r2468choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2468targets, c10r2468choice, ?_, checked⟩
    intro S h
    simp only [c10r2468targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 18 _ (by rfl)
  have c10r2469_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c10r2469targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c10r2469choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r2469targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] c10r2469choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2469targets, c10r2469choice, ?_, checked⟩
    intro S h
    simp only [c10r2469targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 21 _ (by rfl)
  have c10r2470_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c10r2470targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c10r2470choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r2470targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] c10r2470choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2470targets, c10r2470choice, ?_, checked⟩
    intro S h
    simp only [c10r2470targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 23 _ (by rfl)
  have c10r2471_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c10r2471targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c10r2471choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2471targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] c10r2471choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2471targets, c10r2471choice, ?_, checked⟩
    intro S h
    simp only [c10r2471targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2464_closed
  · subst row; exact c10r2465_closed
  · subst row; exact c10r2466_closed
  · subst row; exact c10r2467_closed
  · subst row; exact c10r2468_closed
  · subst row; exact c10r2469_closed
  · subst row; exact c10r2470_closed
  · subst row; exact c10r2471_closed
theorem C10R02464G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2472_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c10r2472targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c10r2472choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2472targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] c10r2472choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2472targets, c10r2472choice, ?_, checked⟩
    intro S h
    simp only [c10r2472targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 30 _ (by rfl)
  have c10r2473_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c10r2473targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c10r2473choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2473targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] c10r2473choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2473targets, c10r2473choice, ?_, checked⟩
    intro S h
    simp only [c10r2473targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 1 _ (by rfl)
  have c10r2474_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c10r2474targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c10r2474choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2474targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] c10r2474choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2474targets, c10r2474choice, ?_, checked⟩
    intro S h
    simp only [c10r2474targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 7 _ (by rfl)
  have c10r2475_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c10r2475targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c10r2475choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2475targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] c10r2475choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2475targets, c10r2475choice, ?_, checked⟩
    intro S h
    simp only [c10r2475targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 13 _ (by rfl)
  have c10r2476_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c10r2476targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c10r2476choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2476targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] c10r2476choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2476targets, c10r2476choice, ?_, checked⟩
    intro S h
    simp only [c10r2476targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 16 _ (by rfl)
  have c10r2477_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c10r2477targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c10r2477choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r2477targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] c10r2477choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2477targets, c10r2477choice, ?_, checked⟩
    intro S h
    simp only [c10r2477targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 18 _ (by rfl)
  have c10r2478_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c10r2478targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c10r2478choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2478targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] c10r2478choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2478targets, c10r2478choice, ?_, checked⟩
    intro S h
    simp only [c10r2478targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 20 _ (by rfl)
  have c10r2479_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c10r2479targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c10r2479choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2479targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] c10r2479choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2479targets, c10r2479choice, ?_, checked⟩
    intro S h
    simp only [c10r2479targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2472_closed
  · subst row; exact c10r2473_closed
  · subst row; exact c10r2474_closed
  · subst row; exact c10r2475_closed
  · subst row; exact c10r2476_closed
  · subst row; exact c10r2477_closed
  · subst row; exact c10r2478_closed
  · subst row; exact c10r2479_closed
theorem C10R02464G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2480_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c10r2480targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c10r2480choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2480targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] c10r2480choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2480targets, c10r2480choice, ?_, checked⟩
    intro S h
    simp only [c10r2480targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 25 _ (by rfl)
  have c10r2481_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c10r2481targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c10r2481choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2481targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] c10r2481choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2481targets, c10r2481choice, ?_, checked⟩
    intro S h
    simp only [c10r2481targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 28 _ (by rfl)
  have c10r2482_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c10r2482targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c10r2482choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2482targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] c10r2482choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2482targets, c10r2482choice, ?_, checked⟩
    intro S h
    simp only [c10r2482targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 31 _ (by rfl)
  have c10r2483_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)] := by
    let c10r2483targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c10r2483choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2483targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)] c10r2483choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2483targets, c10r2483choice, ?_, checked⟩
    intro S h
    simp only [c10r2483targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 4 _ (by rfl)
  have c10r2484_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c10r2484targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c10r2484choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2484targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)] c10r2484choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2484targets, c10r2484choice, ?_, checked⟩
    intro S h
    simp only [c10r2484targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 8 _ (by rfl)
  have c10r2485_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c10r2485targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c10r2485choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2485targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)] c10r2485choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2485targets, c10r2485choice, ?_, checked⟩
    intro S h
    simp only [c10r2485targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 10 _ (by rfl)
  have c10r2486_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c10r2486targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c10r2486choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2486targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)] c10r2486choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2486targets, c10r2486choice, ?_, checked⟩
    intro S h
    simp only [c10r2486targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 12 _ (by rfl)
  have c10r2487_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c10r2487targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c10r2487choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2487targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] c10r2487choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2487targets, c10r2487choice, ?_, checked⟩
    intro S h
    simp only [c10r2487targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2480_closed
  · subst row; exact c10r2481_closed
  · subst row; exact c10r2482_closed
  · subst row; exact c10r2483_closed
  · subst row; exact c10r2484_closed
  · subst row; exact c10r2485_closed
  · subst row; exact c10r2486_closed
  · subst row; exact c10r2487_closed
theorem C10R02464G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2488_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c10r2488targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c10r2488choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2488targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)] c10r2488choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2488targets, c10r2488choice, ?_, checked⟩
    intro S h
    simp only [c10r2488targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 18 _ (by rfl)
  have c10r2489_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c10r2489targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c10r2489choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2489targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)] c10r2489choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2489targets, c10r2489choice, ?_, checked⟩
    intro S h
    simp only [c10r2489targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 21 _ (by rfl)
  have c10r2490_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c10r2490targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c10r2490choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2490targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] c10r2490choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2490targets, c10r2490choice, ?_, checked⟩
    intro S h
    simp only [c10r2490targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 24 _ (by rfl)
  have c10r2491_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c10r2491targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c10r2491choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2491targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] c10r2491choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2491targets, c10r2491choice, ?_, checked⟩
    intro S h
    simp only [c10r2491targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 27 _ (by rfl)
  have c10r2492_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c10r2492targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c10r2492choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2492targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] c10r2492choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2492targets, c10r2492choice, ?_, checked⟩
    intro S h
    simp only [c10r2492targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 0 _ (by rfl)
  have c10r2493_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c10r2493targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c10r2493choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2493targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] c10r2493choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2493targets, c10r2493choice, ?_, checked⟩
    intro S h
    simp only [c10r2493targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 2 _ (by rfl)
  have c10r2494_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c10r2494targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c10r2494choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2494targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] c10r2494choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2494targets, c10r2494choice, ?_, checked⟩
    intro S h
    simp only [c10r2494targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 4 _ (by rfl)
  have c10r2495_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c10r2495targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c10r2495choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (2,(1,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2495targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] c10r2495choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2495targets, c10r2495choice, ?_, checked⟩
    intro S h
    simp only [c10r2495targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,true,false,false,false,false,true,true,true,false] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2488_closed
  · subst row; exact c10r2489_closed
  · subst row; exact c10r2490_closed
  · subst row; exact c10r2491_closed
  · subst row; exact c10r2492_closed
  · subst row; exact c10r2493_closed
  · subst row; exact c10r2494_closed
  · subst row; exact c10r2495_closed
theorem C10R02464_closed (row : List GridPoint) (h : FamilyMember row F10B001L13) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B001L13, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R02464G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02464G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02464G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02464G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02464G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02464G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02464G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02464G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02464G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02464G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02464G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02464G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02464G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02464G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02464G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02464G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02464G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02464G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02464G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02464G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02464G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02464G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02464G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02464G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02464G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02464G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02464G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02464G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02464G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02464G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02464G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02464G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
