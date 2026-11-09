import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R00416G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r416_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6)] := by
    let c10r416targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c10r416choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r416targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6)] c10r416choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r416targets, c10r416choice, ?_, checked⟩
    intro S h
    simp only [c10r416targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 9 _ (by rfl)
  have c10r417_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7)] := by
    let c10r417targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,1),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7),(2,7)]]
    let c10r417choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r417targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7)] c10r417choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r417targets, c10r417choice, ?_, checked⟩
    intro S h
    simp only [c10r417targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 14 _ (by rfl)
  have c10r418_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,4)] := by
    let c10r418targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,1),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,4),(3,4)]]
    let c10r418choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r418targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,4)] c10r418choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r418targets, c10r418choice, ?_, checked⟩
    intro S h
    simp only [c10r418targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 18 _ (by rfl)
  have c10r419_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,5)] := by
    let c10r419targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,1),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,5),(3,5)]]
    let c10r419choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r419targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,5)] c10r419choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r419targets, c10r419choice, ?_, checked⟩
    intro S h
    simp only [c10r419targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 20 _ (by rfl)
  have c10r420_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,6)] := by
    let c10r420targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,1),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,6),(3,6)]]
    let c10r420choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r420targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,4),(1,5),(1,6),(2,6)] c10r420choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r420targets, c10r420choice, ?_, checked⟩
    intro S h
    simp only [c10r420targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 22 _ (by rfl)
  have c10r421_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,4),(1,5),(1,6),(1,7)] := by
    let c10r421targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,7),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,7),(2,4),(2,5),(2,6),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,7),(2,4),(2,5),(2,6),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,7),(2,4),(2,5),(2,6),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,7),(2,4),(2,5),(2,6),(2,7)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,7),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,0),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,1),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,2),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,4),(1,5),(1,6),(1,7),(2,7)]]
    let c10r421choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 8) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 7) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (16,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r421targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,4),(1,5),(1,6),(1,7)] c10r421choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r421targets, c10r421choice, ?_, checked⟩
    intro S h
    simp only [c10r421targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 1 _ (by rfl)
  have c10r422_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c10r422targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c10r422choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r422targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)] c10r422choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r422targets, c10r422choice, ?_, checked⟩
    intro S h
    simp only [c10r422targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 8 _ (by rfl)
  have c10r423_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)] := by
    let c10r423targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
    let c10r423choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r423targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)] c10r423choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r423targets, c10r423choice, ?_, checked⟩
    intro S h
    simp only [c10r423targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r416_closed
  · subst row; exact c10r417_closed
  · subst row; exact c10r418_closed
  · subst row; exact c10r419_closed
  · subst row; exact c10r420_closed
  · subst row; exact c10r421_closed
  · subst row; exact c10r422_closed
  · subst row; exact c10r423_closed
theorem C10R00416G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r424_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)] := by
    let c10r424targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c10r424choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c10r424targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)] c10r424choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r424targets, c10r424choice, ?_, checked⟩
    intro S h
    simp only [c10r424targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 15 _ (by rfl)
  have c10r425_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)] := by
    let c10r425targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c10r425choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c10r425targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)] c10r425choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r425targets, c10r425choice, ?_, checked⟩
    intro S h
    simp only [c10r425targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 17 _ (by rfl)
  have c10r426_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)] := by
    let c10r426targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c10r426choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r426targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)] c10r426choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r426targets, c10r426choice, ?_, checked⟩
    intro S h
    simp only [c10r426targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 19 _ (by rfl)
  have c10r427_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)] := by
    let c10r427targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,5)]]
    let c10r427choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r427targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)] c10r427choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r427targets, c10r427choice, ?_, checked⟩
    intro S h
    simp only [c10r427targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 25 _ (by rfl)
  have c10r428_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)] := by
    let c10r428targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(3,0)]]
    let c10r428choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r428targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)] c10r428choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r428targets, c10r428choice, ?_, checked⟩
    intro S h
    simp only [c10r428targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 29 _ (by rfl)
  have c10r429_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)] := by
    let c10r429targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(3,1)]]
    let c10r429choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r429targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)] c10r429choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r429targets, c10r429choice, ?_, checked⟩
    intro S h
    simp only [c10r429targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 0 _ (by rfl)
  have c10r430_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)] := by
    let c10r430targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(3,2)]]
    let c10r430choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r430targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)] c10r430choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r430targets, c10r430choice, ?_, checked⟩
    intro S h
    simp only [c10r430targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 3 _ (by rfl)
  have c10r431_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)] := by
    let c10r431targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4),(3,4)]]
    let c10r431choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r431targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)] c10r431choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r431targets, c10r431choice, ?_, checked⟩
    intro S h
    simp only [c10r431targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r424_closed
  · subst row; exact c10r425_closed
  · subst row; exact c10r426_closed
  · subst row; exact c10r427_closed
  · subst row; exact c10r428_closed
  · subst row; exact c10r429_closed
  · subst row; exact c10r430_closed
  · subst row; exact c10r431_closed
theorem C10R00416G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r432_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)] := by
    let c10r432targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]]
    let c10r432choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r432targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)] c10r432choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r432targets, c10r432choice, ?_, checked⟩
    intro S h
    simp only [c10r432targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 9 _ (by rfl)
  have c10r433_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)] := by
    let c10r433targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]]
    let c10r433choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r433targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)] c10r433choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r433targets, c10r433choice, ?_, checked⟩
    intro S h
    simp only [c10r433targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 12 _ (by rfl)
  have c10r434_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)] := by
    let c10r434targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]]
    let c10r434choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r434targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)] c10r434choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r434targets, c10r434choice, ?_, checked⟩
    intro S h
    simp only [c10r434targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 14 _ (by rfl)
  have c10r435_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)] := by
    let c10r435targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]]
    let c10r435choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r435targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)] c10r435choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r435targets, c10r435choice, ?_, checked⟩
    intro S h
    simp only [c10r435targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 17 _ (by rfl)
  have c10r436_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)] := by
    let c10r436targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]]
    let c10r436choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r436targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)] c10r436choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r436targets, c10r436choice, ?_, checked⟩
    intro S h
    simp only [c10r436targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 20 _ (by rfl)
  have c10r437_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)] := by
    let c10r437targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]]
    let c10r437choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r437targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)] c10r437choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r437targets, c10r437choice, ?_, checked⟩
    intro S h
    simp only [c10r437targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 23 _ (by rfl)
  have c10r438_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)] := by
    let c10r438targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]
    let c10r438choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r438targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)] c10r438choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r438targets, c10r438choice, ?_, checked⟩
    intro S h
    simp only [c10r438targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 26 _ (by rfl)
  have c10r439_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5)] := by
    let c10r439targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,5)]]
    let c10r439choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r439targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5)] c10r439choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r439targets, c10r439choice, ?_, checked⟩
    intro S h
    simp only [c10r439targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r432_closed
  · subst row; exact c10r433_closed
  · subst row; exact c10r434_closed
  · subst row; exact c10r435_closed
  · subst row; exact c10r436_closed
  · subst row; exact c10r437_closed
  · subst row; exact c10r438_closed
  · subst row; exact c10r439_closed
theorem C10R00416G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r440_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0)] := by
    let c10r440targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(3,0)]]
    let c10r440choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r440targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0)] c10r440choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r440targets, c10r440choice, ?_, checked⟩
    intro S h
    simp only [c10r440targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 4 _ (by rfl)
  have c10r441_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1)] := by
    let c10r441targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(3,1)]]
    let c10r441choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r441targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1)] c10r441choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r441targets, c10r441choice, ?_, checked⟩
    intro S h
    simp only [c10r441targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 8 _ (by rfl)
  have c10r442_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3)] := by
    let c10r442targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3)]]
    let c10r442choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r442targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3)] c10r442choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r442targets, c10r442choice, ?_, checked⟩
    intro S h
    simp only [c10r442targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 11 _ (by rfl)
  have c10r443_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4)] := by
    let c10r443targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4)]]
    let c10r443choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r443targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4)] c10r443choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r443targets, c10r443choice, ?_, checked⟩
    intro S h
    simp only [c10r443targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 13 _ (by rfl)
  have c10r444_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1)] := by
    let c10r444targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(3,1)]]
    let c10r444choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r444targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1)] c10r444choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r444targets, c10r444choice, ?_, checked⟩
    intro S h
    simp only [c10r444targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 17 _ (by rfl)
  have c10r445_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3)] := by
    let c10r445targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(3,3)]]
    let c10r445choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r445targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3)] c10r445choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r445targets, c10r445choice, ?_, checked⟩
    intro S h
    simp only [c10r445targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 21 _ (by rfl)
  have c10r446_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0)] := by
    let c10r446targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0),(4,0)]]
    let c10r446choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r446targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0)] c10r446choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r446targets, c10r446choice, ?_, checked⟩
    intro S h
    simp only [c10r446targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 23 _ (by rfl)
  have c10r447_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2)] := by
    let c10r447targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(3,2)]]
    let c10r447choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r447targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2)] c10r447choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r447targets, c10r447choice, ?_, checked⟩
    intro S h
    simp only [c10r447targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r440_closed
  · subst row; exact c10r441_closed
  · subst row; exact c10r442_closed
  · subst row; exact c10r443_closed
  · subst row; exact c10r444_closed
  · subst row; exact c10r445_closed
  · subst row; exact c10r446_closed
  · subst row; exact c10r447_closed
theorem C10R00416_closed (row : List GridPoint) (h : FamilyMember row F10B000L13) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L13, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R00416G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00416G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00416G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00416G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00416G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00416G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00416G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00416G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00416G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00416G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00416G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00416G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00416G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00416G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00416G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00416G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00416G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00416G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00416G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00416G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00416G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00416G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00416G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00416G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00416G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00416G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00416G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00416G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00416G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00416G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00416G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00416G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
