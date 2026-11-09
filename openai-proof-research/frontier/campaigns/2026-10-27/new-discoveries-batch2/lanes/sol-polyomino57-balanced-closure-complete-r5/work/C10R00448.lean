import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R00448G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r448_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3)] := by
    let c10r448targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3),(3,3)]]
    let c10r448choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r448targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3)] c10r448choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r448targets, c10r448choice, ?_, checked⟩
    intro S h
    simp only [c10r448targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 29 _ (by rfl)
  have c10r449_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1)] := by
    let c10r449targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1),(4,1)]]
    let c10r449choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r449targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1)] c10r449choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r449targets, c10r449choice, ?_, checked⟩
    intro S h
    simp only [c10r449targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 0 _ (by rfl)
  have c10r450_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3)] := by
    let c10r450targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3)]]
    let c10r450choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r450targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3)] c10r450choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r450targets, c10r450choice, ?_, checked⟩
    intro S h
    simp only [c10r450targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 3 _ (by rfl)
  have c10r451_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4)] := by
    let c10r451targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4),(3,4)]]
    let c10r451choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r451targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4)] c10r451choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r451targets, c10r451choice, ?_, checked⟩
    intro S h
    simp only [c10r451targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 6 _ (by rfl)
  have c10r452_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3)] := by
    let c10r452targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3),(4,3)]]
    let c10r452choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r452targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3)] c10r452choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r452targets, c10r452choice, ?_, checked⟩
    intro S h
    simp only [c10r452targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 9 _ (by rfl)
  have c10r453_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6)] := by
    let c10r453targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,1),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,6)]]
    let c10r453choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r453targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6)] c10r453choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r453targets, c10r453choice, ?_, checked⟩
    intro S h
    simp only [c10r453targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 15 _ (by rfl)
  have c10r454_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0)] := by
    let c10r454targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(3,0)]]
    let c10r454choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r454targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0)] c10r454choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r454targets, c10r454choice, ?_, checked⟩
    intro S h
    simp only [c10r454targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 19 _ (by rfl)
  have c10r455_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1)] := by
    let c10r455targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(3,1)]]
    let c10r455choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r455targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1)] c10r455choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r455targets, c10r455choice, ?_, checked⟩
    intro S h
    simp only [c10r455targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r448_closed
  · subst row; exact c10r449_closed
  · subst row; exact c10r450_closed
  · subst row; exact c10r451_closed
  · subst row; exact c10r452_closed
  · subst row; exact c10r453_closed
  · subst row; exact c10r454_closed
  · subst row; exact c10r455_closed
theorem C10R00448G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r456_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4)] := by
    let c10r456targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4),(3,4)]]
    let c10r456choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r456targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4)] c10r456choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r456targets, c10r456choice, ?_, checked⟩
    intro S h
    simp only [c10r456targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 26 _ (by rfl)
  have c10r457_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5)] := by
    let c10r457targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5),(3,5)]]
    let c10r457choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r457targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5)] c10r457choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r457targets, c10r457choice, ?_, checked⟩
    intro S h
    simp only [c10r457targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 28 _ (by rfl)
  have c10r458_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1)] := by
    let c10r458targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(3,1)]]
    let c10r458choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r458targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1)] c10r458choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r458targets, c10r458choice, ?_, checked⟩
    intro S h
    simp only [c10r458targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 0 _ (by rfl)
  have c10r459_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4)] := by
    let c10r459targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(3,4)]]
    let c10r459choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r459targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4)] c10r459choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r459targets, c10r459choice, ?_, checked⟩
    intro S h
    simp only [c10r459targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 4 _ (by rfl)
  have c10r460_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0)] := by
    let c10r460targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0),(4,0)]]
    let c10r460choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r460targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0)] c10r460choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r460targets, c10r460choice, ?_, checked⟩
    intro S h
    simp only [c10r460targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 6 _ (by rfl)
  have c10r461_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2)] := by
    let c10r461targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(3,2)]]
    let c10r461choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r461targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2)] c10r461choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r461targets, c10r461choice, ?_, checked⟩
    intro S h
    simp only [c10r461targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 10 _ (by rfl)
  have c10r462_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4)] := by
    let c10r462targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4),(3,4)]]
    let c10r462choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r462targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4)] c10r462choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r462targets, c10r462choice, ?_, checked⟩
    intro S h
    simp only [c10r462targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 14 _ (by rfl)
  have c10r463_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1)] := by
    let c10r463targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1),(4,1)]]
    let c10r463choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r463targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1)] c10r463choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r463targets, c10r463choice, ?_, checked⟩
    intro S h
    simp only [c10r463targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r456_closed
  · subst row; exact c10r457_closed
  · subst row; exact c10r458_closed
  · subst row; exact c10r459_closed
  · subst row; exact c10r460_closed
  · subst row; exact c10r461_closed
  · subst row; exact c10r462_closed
  · subst row; exact c10r463_closed
theorem C10R00448G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r464_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4)] := by
    let c10r464targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(3,4)]]
    let c10r464choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r464targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4)] c10r464choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r464targets, c10r464choice, ?_, checked⟩
    intro S h
    simp only [c10r464targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 21 _ (by rfl)
  have c10r465_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5)] := by
    let c10r465targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(3,5)]]
    let c10r465choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r465targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5)] c10r465choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r465targets, c10r465choice, ?_, checked⟩
    intro S h
    simp only [c10r465targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 24 _ (by rfl)
  have c10r466_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4)] := by
    let c10r466targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4),(4,4)]]
    let c10r466choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r466targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4)] c10r466choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r466targets, c10r466choice, ?_, checked⟩
    intro S h
    simp only [c10r466targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 27 _ (by rfl)
  have c10r467_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2)] := by
    let c10r467targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]]
    let c10r467choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r467targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2)] c10r467choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r467targets, c10r467choice, ?_, checked⟩
    intro S h
    simp only [c10r467targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 31 _ (by rfl)
  have c10r468_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0)] := by
    let c10r468targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]]
    let c10r468choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r468targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0)] c10r468choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r468targets, c10r468choice, ?_, checked⟩
    intro S h
    simp only [c10r468targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 1 _ (by rfl)
  have c10r469_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1)] := by
    let c10r469targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]]
    let c10r469choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r469targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1)] c10r469choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r469targets, c10r469choice, ?_, checked⟩
    intro S h
    simp only [c10r469targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 3 _ (by rfl)
  have c10r470_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1)] := by
    let c10r470targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]]
    let c10r470choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r470targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1)] c10r470choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r470targets, c10r470choice, ?_, checked⟩
    intro S h
    simp only [c10r470targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 6 _ (by rfl)
  have c10r471_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0)] := by
    let c10r471targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]]
    let c10r471choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r471targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0)] c10r471choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r471targets, c10r471choice, ?_, checked⟩
    intro S h
    simp only [c10r471targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r464_closed
  · subst row; exact c10r465_closed
  · subst row; exact c10r466_closed
  · subst row; exact c10r467_closed
  · subst row; exact c10r468_closed
  · subst row; exact c10r469_closed
  · subst row; exact c10r470_closed
  · subst row; exact c10r471_closed
theorem C10R00448G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r472_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3)] := by
    let c10r472targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]]
    let c10r472choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r472targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3)] c10r472choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r472targets, c10r472choice, ?_, checked⟩
    intro S h
    simp only [c10r472targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 12 _ (by rfl)
  have c10r473_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1)] := by
    let c10r473targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]]
    let c10r473choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r473targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1)] c10r473choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r473targets, c10r473choice, ?_, checked⟩
    intro S h
    simp only [c10r473targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 15 _ (by rfl)
  have c10r474_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2)] := by
    let c10r474targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]]
    let c10r474choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r474targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2)] c10r474choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r474targets, c10r474choice, ?_, checked⟩
    intro S h
    simp only [c10r474targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 17 _ (by rfl)
  have c10r475_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1)] := by
    let c10r475targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]]
    let c10r475choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r475targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1)] c10r475choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r475targets, c10r475choice, ?_, checked⟩
    intro S h
    simp only [c10r475targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 20 _ (by rfl)
  have c10r476_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2)] := by
    let c10r476targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]]
    let c10r476choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r476targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2)] c10r476choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r476targets, c10r476choice, ?_, checked⟩
    intro S h
    simp only [c10r476targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 23 _ (by rfl)
  have c10r477_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1)] := by
    let c10r477targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]]
    let c10r477choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r477targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1)] c10r477choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r477targets, c10r477choice, ?_, checked⟩
    intro S h
    simp only [c10r477targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 26 _ (by rfl)
  have c10r478_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5)] := by
    let c10r478targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c10r478choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r478targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5)] c10r478choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r478targets, c10r478choice, ?_, checked⟩
    intro S h
    simp only [c10r478targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 0 _ (by rfl)
  have c10r479_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0)] := by
    let c10r479targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c10r479choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r479targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0)] c10r479choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r479targets, c10r479choice, ?_, checked⟩
    intro S h
    simp only [c10r479targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r472_closed
  · subst row; exact c10r473_closed
  · subst row; exact c10r474_closed
  · subst row; exact c10r475_closed
  · subst row; exact c10r476_closed
  · subst row; exact c10r477_closed
  · subst row; exact c10r478_closed
  · subst row; exact c10r479_closed
theorem C10R00448_closed (row : List GridPoint) (h : FamilyMember row F10B000L14) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L14, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R00448G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00448G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00448G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00448G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00448G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00448G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00448G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00448G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00448G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00448G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00448G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00448G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00448G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00448G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00448G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00448G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00448G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00448G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00448G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00448G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00448G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00448G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00448G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00448G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00448G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00448G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00448G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00448G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00448G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00448G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00448G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00448G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
