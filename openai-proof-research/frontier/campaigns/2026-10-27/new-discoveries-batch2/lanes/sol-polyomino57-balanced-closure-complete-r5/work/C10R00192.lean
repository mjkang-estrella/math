import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R00192G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r192_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(3,0)] := by
    let c10r192targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0),(4,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(3,0),(4,0)]]
    let c10r192choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r192targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(3,0)] c10r192choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r192targets, c10r192choice, ?_, checked⟩
    intro S h
    simp only [c10r192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 30 _ (by rfl)
  have c10r193_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2)] := by
    let c10r193targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,1),(3,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2),(3,2)]]
    let c10r193choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r193targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2)] c10r193choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r193targets, c10r193choice, ?_, checked⟩
    intro S h
    simp only [c10r193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 1 _ (by rfl)
  have c10r194_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(2,3)] := by
    let c10r194targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(2,3),(3,3)]]
    let c10r194choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r194targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(2,3)] c10r194choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r194targets, c10r194choice, ?_, checked⟩
    intro S h
    simp only [c10r194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 4 _ (by rfl)
  have c10r195_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(3,2)] := by
    let c10r195targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(4,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(3,2),(4,2)]]
    let c10r195choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r195targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(3,2)] c10r195choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r195targets, c10r195choice, ?_, checked⟩
    intro S h
    simp only [c10r195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 7 _ (by rfl)
  have c10r196_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5)] := by
    let c10r196targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,5)]]
    let c10r196choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r196targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5)] c10r196choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r196targets, c10r196choice, ?_, checked⟩
    intro S h
    simp only [c10r196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 12 _ (by rfl)
  have c10r197_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0)] := by
    let c10r197targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(3,0)]]
    let c10r197choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r197targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0)] c10r197choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r197targets, c10r197choice, ?_, checked⟩
    intro S h
    simp only [c10r197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 16 _ (by rfl)
  have c10r198_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3)] := by
    let c10r198targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3),(3,3)]]
    let c10r198choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r198targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3)] c10r198choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r198targets, c10r198choice, ?_, checked⟩
    intro S h
    simp only [c10r198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 19 _ (by rfl)
  have c10r199_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4)] := by
    let c10r199targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4),(3,4)]]
    let c10r199choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r199targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4)] c10r199choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r199targets, c10r199choice, ?_, checked⟩
    intro S h
    simp only [c10r199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r192_closed
  · subst row; exact c10r193_closed
  · subst row; exact c10r194_closed
  · subst row; exact c10r195_closed
  · subst row; exact c10r196_closed
  · subst row; exact c10r197_closed
  · subst row; exact c10r198_closed
  · subst row; exact c10r199_closed
theorem C10R00192G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r200_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6)] := by
    let c10r200targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,5),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,6)]]
    let c10r200choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r200targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6)] c10r200choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r200targets, c10r200choice, ?_, checked⟩
    intro S h
    simp only [c10r200targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 26 _ (by rfl)
  have c10r201_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0)] := by
    let c10r201targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(3,0)]]
    let c10r201choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r201targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0)] c10r201choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r201targets, c10r201choice, ?_, checked⟩
    intro S h
    simp only [c10r201targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 30 _ (by rfl)
  have c10r202_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3)] := by
    let c10r202targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,5),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3),(3,3)]]
    let c10r202choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r202targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3)] c10r202choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r202targets, c10r202choice, ?_, checked⟩
    intro S h
    simp only [c10r202targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 2 _ (by rfl)
  have c10r203_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,5)] := by
    let c10r203targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,5),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,5),(3,5)]]
    let c10r203choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r203targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,5)] c10r203choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r203targets, c10r203choice, ?_, checked⟩
    intro S h
    simp only [c10r203targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 5 _ (by rfl)
  have c10r204_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1)] := by
    let c10r204targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(3,1)]]
    let c10r204choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r204targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1)] c10r204choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r204targets, c10r204choice, ?_, checked⟩
    intro S h
    simp only [c10r204targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 9 _ (by rfl)
  have c10r205_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3)] := by
    let c10r205targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(3,3)]]
    let c10r205choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r205targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3)] c10r205choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r205targets, c10r205choice, ?_, checked⟩
    intro S h
    simp only [c10r205targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 13 _ (by rfl)
  have c10r206_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0)] := by
    let c10r206targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(4,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0),(4,0)]]
    let c10r206choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r206targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0)] c10r206choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r206targets, c10r206choice, ?_, checked⟩
    intro S h
    simp only [c10r206targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 15 _ (by rfl)
  have c10r207_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3)] := by
    let c10r207targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,2),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3),(3,3)]]
    let c10r207choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r207targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3)] c10r207choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r207targets, c10r207choice, ?_, checked⟩
    intro S h
    simp only [c10r207targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r200_closed
  · subst row; exact c10r201_closed
  · subst row; exact c10r202_closed
  · subst row; exact c10r203_closed
  · subst row; exact c10r204_closed
  · subst row; exact c10r205_closed
  · subst row; exact c10r206_closed
  · subst row; exact c10r207_closed
theorem C10R00192G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r208_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4)] := by
    let c10r208targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4),(3,4)]]
    let c10r208choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r208targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4)] c10r208choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r208targets, c10r208choice, ?_, checked⟩
    intro S h
    simp only [c10r208targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 22 _ (by rfl)
  have c10r209_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,3)] := by
    let c10r209targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(4,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,3),(4,3)]]
    let c10r209choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r209targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,3)] c10r209choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r209targets, c10r209choice, ?_, checked⟩
    intro S h
    simp only [c10r209targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 25 _ (by rfl)
  have c10r210_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6)] := by
    let c10r210targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,6)]]
    let c10r210choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r210targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6)] c10r210choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r210targets, c10r210choice, ?_, checked⟩
    intro S h
    simp only [c10r210targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 30 _ (by rfl)
  have c10r211_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0)] := by
    let c10r211targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(3,0)]]
    let c10r211choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r211targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0)] c10r211choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r211targets, c10r211choice, ?_, checked⟩
    intro S h
    simp only [c10r211targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 2 _ (by rfl)
  have c10r212_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4)] := by
    let c10r212targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4),(3,4)]]
    let c10r212choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r212targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4)] c10r212choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r212targets, c10r212choice, ?_, checked⟩
    intro S h
    simp only [c10r212targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 5 _ (by rfl)
  have c10r213_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5)] := by
    let c10r213targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,5),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5),(3,5)]]
    let c10r213choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r213targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5)] c10r213choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r213targets, c10r213choice, ?_, checked⟩
    intro S h
    simp only [c10r213targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 7 _ (by rfl)
  have c10r214_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1)] := by
    let c10r214targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(3,1)]]
    let c10r214choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r214targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1)] c10r214choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r214targets, c10r214choice, ?_, checked⟩
    intro S h
    simp only [c10r214targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 11 _ (by rfl)
  have c10r215_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4)] := by
    let c10r215targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(3,4)]]
    let c10r215choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r215targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4)] c10r215choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r215targets, c10r215choice, ?_, checked⟩
    intro S h
    simp only [c10r215targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r208_closed
  · subst row; exact c10r209_closed
  · subst row; exact c10r210_closed
  · subst row; exact c10r211_closed
  · subst row; exact c10r212_closed
  · subst row; exact c10r213_closed
  · subst row; exact c10r214_closed
  · subst row; exact c10r215_closed
theorem C10R00192G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,6)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r216_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0)] := by
    let c10r216targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(4,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0),(4,0)]]
    let c10r216choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r216targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0)] c10r216choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r216targets, c10r216choice, ?_, checked⟩
    intro S h
    simp only [c10r216targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 17 _ (by rfl)
  have c10r217_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4)] := by
    let c10r217targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,3),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4),(3,4)]]
    let c10r217choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r217targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4)] c10r217choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r217targets, c10r217choice, ?_, checked⟩
    intro S h
    simp only [c10r217targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 21 _ (by rfl)
  have c10r218_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5)] := by
    let c10r218targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(3,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5),(3,5)]]
    let c10r218choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r218targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5)] c10r218choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r218targets, c10r218choice, ?_, checked⟩
    intro S h
    simp only [c10r218targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 24 _ (by rfl)
  have c10r219_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,4)] := by
    let c10r219targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(4,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,4),(4,4)]]
    let c10r219choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r219targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,4)] c10r219choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r219targets, c10r219choice, ?_, checked⟩
    intro S h
    simp only [c10r219targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 27 _ (by rfl)
  have c10r220_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7)] := by
    let c10r220targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(2,7)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,0),(1,5),(1,6),(1,7)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7),(2,7)]]
    let c10r220choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (11,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (16,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r220targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7)] c10r220choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r220targets, c10r220choice, ?_, checked⟩
    intro S h
    simp only [c10r220targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 0 _ (by rfl)
  have c10r221_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0)] := by
    let c10r221targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(1,6),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(1,7),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0),(3,0)]]
    let c10r221choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (11,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (14,(0,1)) else (15,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r221targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0)] c10r221choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r221targets, c10r221choice, ?_, checked⟩
    intro S h
    simp only [c10r221targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 4 _ (by rfl)
  have c10r222_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,5)] := by
    let c10r222targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(1,6),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,5),(3,5)]]
    let c10r222choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r222targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,5)] c10r222choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r222targets, c10r222choice, ?_, checked⟩
    intro S h
    simp only [c10r222targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 7 _ (by rfl)
  have c10r223_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,6)] := by
    let c10r223targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(1,6),(2,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,6),(3,6)]]
    let c10r223choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (4,(1,0)) else (5,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r223targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,6)] c10r223choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r223targets, c10r223choice, ?_, checked⟩
    intro S h
    simp only [c10r223targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,true,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r216_closed
  · subst row; exact c10r217_closed
  · subst row; exact c10r218_closed
  · subst row; exact c10r219_closed
  · subst row; exact c10r220_closed
  · subst row; exact c10r221_closed
  · subst row; exact c10r222_closed
  · subst row; exact c10r223_closed
theorem C10R00192_closed (row : List GridPoint) (h : FamilyMember row F10B000L6) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L6, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R00192G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00192G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00192G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00192G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00192G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00192G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00192G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00192G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00192G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00192G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00192G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00192G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00192G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00192G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00192G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00192G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00192G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00192G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00192G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00192G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00192G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00192G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00192G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00192G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00192G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00192G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00192G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00192G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00192G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00192G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00192G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00192G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
