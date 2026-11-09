import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R02080G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2080_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)] := by
    let c10r2080targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(6,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2),(6,2)]]
    let c10r2080choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2080targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)] c10r2080choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2080targets, c10r2080choice, ?_, checked⟩
    intro S h
    simp only [c10r2080targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 24 _ (by rfl)
  have c10r2081_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)] := by
    let c10r2081targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4),(5,4)]]
    let c10r2081choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r2081targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)] c10r2081choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2081targets, c10r2081choice, ?_, checked⟩
    intro S h
    simp only [c10r2081targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 27 _ (by rfl)
  have c10r2082_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)] := by
    let c10r2082targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(6,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(6,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(6,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3),(6,3)]]
    let c10r2082choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2082targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)] c10r2082choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2082targets, c10r2082choice, ?_, checked⟩
    intro S h
    simp only [c10r2082targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 30 _ (by rfl)
  have c10r2083_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)] := by
    let c10r2083targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(4,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(4,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(4,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,6),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6),(4,6)]]
    let c10r2083choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (17,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r2083targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)] c10r2083choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2083targets, c10r2083choice, ?_, checked⟩
    intro S h
    simp only [c10r2083targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 3 _ (by rfl)
  have c10r2084_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)] := by
    let c10r2084targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(3,6),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3),(5,3)]]
    let c10r2084choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2084targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)] c10r2084choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2084targets, c10r2084choice, ?_, checked⟩
    intro S h
    simp only [c10r2084targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 7 _ (by rfl)
  have c10r2085_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)] := by
    let c10r2085targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4),(5,4)]]
    let c10r2085choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r2085targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)] c10r2085choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2085targets, c10r2085choice, ?_, checked⟩
    intro S h
    simp only [c10r2085targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 9 _ (by rfl)
  have c10r2086_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)] := by
    let c10r2086targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(3,6),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5),(5,5)]]
    let c10r2086choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (16,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2086targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)] c10r2086choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2086targets, c10r2086choice, ?_, checked⟩
    intro S h
    simp only [c10r2086targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 11 _ (by rfl)
  have c10r2087_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)] := by
    let c10r2087targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,2),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(5,3)]]
    let c10r2087choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r2087targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)] c10r2087choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2087targets, c10r2087choice, ?_, checked⟩
    intro S h
    simp only [c10r2087targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2080_closed
  · subst row; exact c10r2081_closed
  · subst row; exact c10r2082_closed
  · subst row; exact c10r2083_closed
  · subst row; exact c10r2084_closed
  · subst row; exact c10r2085_closed
  · subst row; exact c10r2086_closed
  · subst row; exact c10r2087_closed
theorem C10R02080G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2088_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)] := by
    let c10r2088targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(5,4)]]
    let c10r2088choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r2088targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)] c10r2088choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2088targets, c10r2088choice, ?_, checked⟩
    intro S h
    simp only [c10r2088targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 18 _ (by rfl)
  have c10r2089_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)] := by
    let c10r2089targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(6,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(6,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(6,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3),(6,3)]]
    let c10r2089choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2089targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)] c10r2089choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2089targets, c10r2089choice, ?_, checked⟩
    intro S h
    simp only [c10r2089targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 21 _ (by rfl)
  have c10r2090_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)] := by
    let c10r2090targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(5,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(5,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(5,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5),(5,5)]]
    let c10r2090choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r2090targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)] c10r2090choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2090targets, c10r2090choice, ?_, checked⟩
    intro S h
    simp only [c10r2090targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 24 _ (by rfl)
  have c10r2091_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)] := by
    let c10r2091targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(6,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(6,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(6,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(6,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5),(4,5),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4),(5,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4),(6,4)]]
    let c10r2091choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2091targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)] c10r2091choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2091targets, c10r2091choice, ?_, checked⟩
    intro S h
    simp only [c10r2091targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 27 _ (by rfl)
  have c10r2092_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)] := by
    let c10r2092targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,1),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,1),(5,2),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,3)]]
    let c10r2092choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (17,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r2092targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)] c10r2092choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2092targets, c10r2092choice, ?_, checked⟩
    intro S h
    simp only [c10r2092targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 1 _ (by rfl)
  have c10r2093_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)] := by
    let c10r2093targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(5,4)]]
    let c10r2093choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (16,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2093targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)] c10r2093choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2093targets, c10r2093choice, ?_, checked⟩
    intro S h
    simp only [c10r2093targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 5 _ (by rfl)
  have c10r2094_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)] := by
    let c10r2094targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(6,2)]]
    let c10r2094choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2094targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)] c10r2094choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2094targets, c10r2094choice, ?_, checked⟩
    intro S h
    simp only [c10r2094targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 8 _ (by rfl)
  have c10r2095_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)] := by
    let c10r2095targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(6,3)]]
    let c10r2095choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2095targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)] c10r2095choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2095targets, c10r2095choice, ?_, checked⟩
    intro S h
    simp only [c10r2095targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2088_closed
  · subst row; exact c10r2089_closed
  · subst row; exact c10r2090_closed
  · subst row; exact c10r2091_closed
  · subst row; exact c10r2092_closed
  · subst row; exact c10r2093_closed
  · subst row; exact c10r2094_closed
  · subst row; exact c10r2095_closed
theorem C10R02080G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2096_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)] := by
    let c10r2096targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(5,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(5,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(5,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,4),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,5),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,5)]]
    let c10r2096choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (17,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r2096targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)] c10r2096choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2096targets, c10r2096choice, ?_, checked⟩
    intro S h
    simp only [c10r2096targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 14 _ (by rfl)
  have c10r2097_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)] := by
    let c10r2097targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(6,3)]]
    let c10r2097choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2097targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)] c10r2097choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2097targets, c10r2097choice, ?_, checked⟩
    intro S h
    simp only [c10r2097targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 17 _ (by rfl)
  have c10r2098_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)] := by
    let c10r2098targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,4),(4,5),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(5,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4),(6,4)]]
    let c10r2098choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r2098targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)] c10r2098choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2098targets, c10r2098choice, ?_, checked⟩
    intro S h
    simp only [c10r2098targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 19 _ (by rfl)
  have c10r2099_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3)] := by
    let c10r2099targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,2),(6,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,2),(6,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,2),(6,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,2),(6,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,4),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,3)]]
    let c10r2099choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (17,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r2099targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3)] c10r2099choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2099targets, c10r2099choice, ?_, checked⟩
    intro S h
    simp only [c10r2099targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 23 _ (by rfl)
  have c10r2100_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4)] := by
    let c10r2100targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(6,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(6,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(6,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(6,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,4),(5,4),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(5,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,4)]]
    let c10r2100choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (17,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 4) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r2100targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4)] c10r2100choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2100targets, c10r2100choice, ?_, checked⟩
    intro S h
    simp only [c10r2100targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 26 _ (by rfl)
  have c10r2101_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3)] := by
    let c10r2101targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,4),(5,4),(6,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(5,4),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,2),(6,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(6,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3)]]
    let c10r2101choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 4) then (18,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 3) then (19,(0,0)) else (20,(0,0)))))))
    have checked : successorFastRowCheck c10r2101targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3)] c10r2101choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2101targets, c10r2101choice, ?_, checked⟩
    intro S h
    simp only [c10r2101targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 29 _ (by rfl)
  have c10r2102_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4)] := by
    let c10r2102targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(2,4)]]
    let c10r2102choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 8) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (6,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r2102targets [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4)] c10r2102choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2102targets, c10r2102choice, ?_, checked⟩
    intro S h
    simp only [c10r2102targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 6 _ (by rfl)
  have c10r2103_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4)] := by
    let c10r2103targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,0),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,0),(2,2),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,0),(2,2),(2,3),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(2,4)]]
    let c10r2103choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2103targets [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4)] c10r2103choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2103targets, c10r2103choice, ?_, checked⟩
    intro S h
    simp only [c10r2103targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2096_closed
  · subst row; exact c10r2097_closed
  · subst row; exact c10r2098_closed
  · subst row; exact c10r2099_closed
  · subst row; exact c10r2100_closed
  · subst row; exact c10r2101_closed
  · subst row; exact c10r2102_closed
  · subst row; exact c10r2103_closed
theorem C10R02080G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r2104_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4)] := by
    let c10r2104targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c10r2104choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2104targets [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4)] c10r2104choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2104targets, c10r2104choice, ?_, checked⟩
    intro S h
    simp only [c10r2104targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 19 _ (by rfl)
  have c10r2105_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5)] := by
    let c10r2105targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c10r2105choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2105targets [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5)] c10r2105choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2105targets, c10r2105choice, ?_, checked⟩
    intro S h
    simp only [c10r2105targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 24 _ (by rfl)
  have c10r2106_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6)] := by
    let c10r2106targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,6)]]
    let c10r2106choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2106targets [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6)] c10r2106choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2106targets, c10r2106choice, ?_, checked⟩
    intro S h
    simp only [c10r2106targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 29 _ (by rfl)
  have c10r2107_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2)] := by
    let c10r2107targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,2)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,2)],[(0,6),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c10r2107choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2107targets [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2)] c10r2107choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2107targets, c10r2107choice, ?_, checked⟩
    intro S h
    simp only [c10r2107targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 1 _ (by rfl)
  have c10r2108_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,3)] := by
    let c10r2108targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,3)],[(0,6),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c10r2108choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2108targets [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,3)] c10r2108choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2108targets, c10r2108choice, ?_, checked⟩
    intro S h
    simp only [c10r2108targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 3 _ (by rfl)
  have c10r2109_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,4)] := by
    let c10r2109targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,4)],[(0,6),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c10r2109choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r2109targets [(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,4)] c10r2109choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2109targets, c10r2109choice, ?_, checked⟩
    intro S h
    simp only [c10r2109targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 5 _ (by rfl)
  have c10r2110_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c10r2110targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c10r2110choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r2110targets [(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)] c10r2110choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2110targets, c10r2110choice, ?_, checked⟩
    intro S h
    simp only [c10r2110targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 12 _ (by rfl)
  have c10r2111_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5)] := by
    let c10r2111targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,5),(0,6),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c10r2111choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r2111targets [(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5)] c10r2111choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r2111targets, c10r2111choice, ?_, checked⟩
    intro S h
    simp only [c10r2111targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,true,false,false,false,true,false] 18 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r2104_closed
  · subst row; exact c10r2105_closed
  · subst row; exact c10r2106_closed
  · subst row; exact c10r2107_closed
  · subst row; exact c10r2108_closed
  · subst row; exact c10r2109_closed
  · subst row; exact c10r2110_closed
  · subst row; exact c10r2111_closed
theorem C10R02080_closed (row : List GridPoint) (h : FamilyMember row F10B001L1) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B001L1, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R02080G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02080G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02080G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02080G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02080G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02080G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02080G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02080G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02080G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02080G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02080G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02080G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02080G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02080G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02080G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02080G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02080G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02080G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02080G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02080G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02080G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02080G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02080G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02080G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R02080G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R02080G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R02080G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R02080G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R02080G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R02080G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R02080G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R02080G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
