import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R01152G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1152_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0)] := by
    let c10r1152targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)]]
    let c10r1152choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1152targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0)] c10r1152choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1152targets, c10r1152choice, ?_, checked⟩
    intro S h
    simp only [c10r1152targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 30 _ (by rfl)
  have c10r1153_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2)] := by
    let c10r1153targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)]]
    let c10r1153choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1153targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2)] c10r1153choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1153targets, c10r1153choice, ?_, checked⟩
    intro S h
    simp only [c10r1153targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
  have c10r1154_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3)] := by
    let c10r1154targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)]]
    let c10r1154choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1154targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3)] c10r1154choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1154targets, c10r1154choice, ?_, checked⟩
    intro S h
    simp only [c10r1154targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 5 _ (by rfl)
  have c10r1155_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4)] := by
    let c10r1155targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)]]
    let c10r1155choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1155targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4)] c10r1155choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1155targets, c10r1155choice, ?_, checked⟩
    intro S h
    simp only [c10r1155targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 8 _ (by rfl)
  have c10r1156_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2)] := by
    let c10r1156targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)]]
    let c10r1156choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1156targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2)] c10r1156choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1156targets, c10r1156choice, ?_, checked⟩
    intro S h
    simp only [c10r1156targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 11 _ (by rfl)
  have c10r1157_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4)] := by
    let c10r1157targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]]
    let c10r1157choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1157targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4)] c10r1157choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1157targets, c10r1157choice, ?_, checked⟩
    intro S h
    simp only [c10r1157targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 14 _ (by rfl)
  have c10r1158_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3)] := by
    let c10r1158targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)]]
    let c10r1158choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1158targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3)] c10r1158choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1158targets, c10r1158choice, ?_, checked⟩
    intro S h
    simp only [c10r1158targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 17 _ (by rfl)
  have c10r1159_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5)] := by
    let c10r1159targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)]]
    let c10r1159choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1159targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5)] c10r1159choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1159targets, c10r1159choice, ?_, checked⟩
    intro S h
    simp only [c10r1159targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1152_closed
  · subst row; exact c10r1153_closed
  · subst row; exact c10r1154_closed
  · subst row; exact c10r1155_closed
  · subst row; exact c10r1156_closed
  · subst row; exact c10r1157_closed
  · subst row; exact c10r1158_closed
  · subst row; exact c10r1159_closed
theorem C10R01152G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1160_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4)] := by
    let c10r1160targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)]]
    let c10r1160choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1160targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4)] c10r1160choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1160targets, c10r1160choice, ?_, checked⟩
    intro S h
    simp only [c10r1160targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 23 _ (by rfl)
  have c10r1161_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c10r1161targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c10r1161choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1161targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] c10r1161choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1161targets, c10r1161choice, ?_, checked⟩
    intro S h
    simp only [c10r1161targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 28 _ (by rfl)
  have c10r1162_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3)] := by
    let c10r1162targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
    let c10r1162choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1162targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3)] c10r1162choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1162targets, c10r1162choice, ?_, checked⟩
    intro S h
    simp only [c10r1162targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 0 _ (by rfl)
  have c10r1163_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0)] := by
    let c10r1163targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
    let c10r1163choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1163targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0)] c10r1163choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1163targets, c10r1163choice, ?_, checked⟩
    intro S h
    simp only [c10r1163targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 2 _ (by rfl)
  have c10r1164_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,1)] := by
    let c10r1164targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
    let c10r1164choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1164targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,1)] c10r1164choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1164targets, c10r1164choice, ?_, checked⟩
    intro S h
    simp only [c10r1164targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 4 _ (by rfl)
  have c10r1165_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3)] := by
    let c10r1165targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)]]
    let c10r1165choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1165targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3)] c10r1165choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1165targets, c10r1165choice, ?_, checked⟩
    intro S h
    simp only [c10r1165targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 8 _ (by rfl)
  have c10r1166_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0)] := by
    let c10r1166targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)]]
    let c10r1166choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1166targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0)] c10r1166choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1166targets, c10r1166choice, ?_, checked⟩
    intro S h
    simp only [c10r1166targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 11 _ (by rfl)
  have c10r1167_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2)] := by
    let c10r1167targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)]]
    let c10r1167choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1167targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2)] c10r1167choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1167targets, c10r1167choice, ?_, checked⟩
    intro S h
    simp only [c10r1167targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1160_closed
  · subst row; exact c10r1161_closed
  · subst row; exact c10r1162_closed
  · subst row; exact c10r1163_closed
  · subst row; exact c10r1164_closed
  · subst row; exact c10r1165_closed
  · subst row; exact c10r1166_closed
  · subst row; exact c10r1167_closed
theorem C10R01152G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1168_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4)] := by
    let c10r1168targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)]]
    let c10r1168choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1168targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4)] c10r1168choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1168targets, c10r1168choice, ?_, checked⟩
    intro S h
    simp only [c10r1168targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 18 _ (by rfl)
  have c10r1169_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0)] := by
    let c10r1169targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)]]
    let c10r1169choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1169targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0)] c10r1169choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1169targets, c10r1169choice, ?_, checked⟩
    intro S h
    simp only [c10r1169targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 21 _ (by rfl)
  have c10r1170_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3)] := by
    let c10r1170targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)]]
    let c10r1170choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1170targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3)] c10r1170choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1170targets, c10r1170choice, ?_, checked⟩
    intro S h
    simp only [c10r1170targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 24 _ (by rfl)
  have c10r1171_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1)] := by
    let c10r1171targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)]]
    let c10r1171choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1171targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1)] c10r1171choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1171targets, c10r1171choice, ?_, checked⟩
    intro S h
    simp only [c10r1171targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 27 _ (by rfl)
  have c10r1172_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0)] := by
    let c10r1172targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)]]
    let c10r1172choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1172targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0)] c10r1172choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1172targets, c10r1172choice, ?_, checked⟩
    intro S h
    simp only [c10r1172targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 29 _ (by rfl)
  have c10r1173_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)] := by
    let c10r1173targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c10r1173choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1173targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)] c10r1173choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1173targets, c10r1173choice, ?_, checked⟩
    intro S h
    simp only [c10r1173targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 1 _ (by rfl)
  have c10r1174_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1)] := by
    let c10r1174targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)]]
    let c10r1174choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1174targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1)] c10r1174choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1174targets, c10r1174choice, ?_, checked⟩
    intro S h
    simp only [c10r1174targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 4 _ (by rfl)
  have c10r1175_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2)] := by
    let c10r1175targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)]]
    let c10r1175choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1175targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2)] c10r1175choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1175targets, c10r1175choice, ?_, checked⟩
    intro S h
    simp only [c10r1175targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1168_closed
  · subst row; exact c10r1169_closed
  · subst row; exact c10r1170_closed
  · subst row; exact c10r1171_closed
  · subst row; exact c10r1172_closed
  · subst row; exact c10r1173_closed
  · subst row; exact c10r1174_closed
  · subst row; exact c10r1175_closed
theorem C10R01152G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1176_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)] := by
    let c10r1176targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)]]
    let c10r1176choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1176targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)] c10r1176choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1176targets, c10r1176choice, ?_, checked⟩
    intro S h
    simp only [c10r1176targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 10 _ (by rfl)
  have c10r1177_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)] := by
    let c10r1177targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c10r1177choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1177targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)] c10r1177choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1177targets, c10r1177choice, ?_, checked⟩
    intro S h
    simp only [c10r1177targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 13 _ (by rfl)
  have c10r1178_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)] := by
    let c10r1178targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c10r1178choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1178targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)] c10r1178choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1178targets, c10r1178choice, ?_, checked⟩
    intro S h
    simp only [c10r1178targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 15 _ (by rfl)
  have c10r1179_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2)] := by
    let c10r1179targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)]]
    let c10r1179choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1179targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2)] c10r1179choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1179targets, c10r1179choice, ?_, checked⟩
    intro S h
    simp only [c10r1179targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 19 _ (by rfl)
  have c10r1180_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3)] := by
    let c10r1180targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)]]
    let c10r1180choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1180targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3)] c10r1180choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1180targets, c10r1180choice, ?_, checked⟩
    intro S h
    simp only [c10r1180targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 22 _ (by rfl)
  have c10r1181_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2)] := by
    let c10r1181targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]
    let c10r1181choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1181targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(3,2),(4,2)] c10r1181choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1181targets, c10r1181choice, ?_, checked⟩
    intro S h
    simp only [c10r1181targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 25 _ (by rfl)
  have c10r1182_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5)] := by
    let c10r1182targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c10r1182choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1182targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5)] c10r1182choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1182targets, c10r1182choice, ?_, checked⟩
    intro S h
    simp only [c10r1182targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 29 _ (by rfl)
  have c10r1183_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)] := by
    let c10r1183targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c10r1183choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1183targets [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)] c10r1183choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1183targets, c10r1183choice, ?_, checked⟩
    intro S h
    simp only [c10r1183targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,false,false,true] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1176_closed
  · subst row; exact c10r1177_closed
  · subst row; exact c10r1178_closed
  · subst row; exact c10r1179_closed
  · subst row; exact c10r1180_closed
  · subst row; exact c10r1181_closed
  · subst row; exact c10r1182_closed
  · subst row; exact c10r1183_closed
theorem C10R01152_closed (row : List GridPoint) (h : FamilyMember row F10B000L36) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L36, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R01152G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01152G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01152G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01152G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01152G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01152G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01152G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01152G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01152G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01152G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01152G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01152G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01152G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01152G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01152G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01152G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01152G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01152G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01152G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01152G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01152G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01152G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01152G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01152G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01152G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01152G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01152G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01152G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01152G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01152G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01152G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01152G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
