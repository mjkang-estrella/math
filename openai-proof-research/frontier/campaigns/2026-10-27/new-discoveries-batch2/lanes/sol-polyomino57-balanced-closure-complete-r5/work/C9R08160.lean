import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08160G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8160_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r8160targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r8160choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8160targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r8160choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8160targets, c9r8160choice, ?_, checked⟩
    intro S h
    simp only [c9r8160targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 22 _ (by rfl)
  have c9r8161_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r8161targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r8161choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8161targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r8161choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8161targets, c9r8161choice, ?_, checked⟩
    intro S h
    simp only [c9r8161targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 25 _ (by rfl)
  have c9r8162_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r8162targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r8162choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8162targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r8162choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8162targets, c9r8162choice, ?_, checked⟩
    intro S h
    simp only [c9r8162targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 27 _ (by rfl)
  have c9r8163_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r8163targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r8163choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8163targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r8163choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8163targets, c9r8163choice, ?_, checked⟩
    intro S h
    simp only [c9r8163targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 29 _ (by rfl)
  have c9r8164_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r8164targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r8164choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8164targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r8164choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8164targets, c9r8164choice, ?_, checked⟩
    intro S h
    simp only [c9r8164targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 0 _ (by rfl)
  have c9r8165_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r8165targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r8165choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8165targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r8165choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8165targets, c9r8165choice, ?_, checked⟩
    intro S h
    simp only [c9r8165targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 3 _ (by rfl)
  have c9r8166_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r8166targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r8166choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8166targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r8166choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8166targets, c9r8166choice, ?_, checked⟩
    intro S h
    simp only [c9r8166targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 5 _ (by rfl)
  have c9r8167_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r8167targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r8167choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8167targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r8167choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8167targets, c9r8167choice, ?_, checked⟩
    intro S h
    simp only [c9r8167targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8160_closed
  · subst row; exact c9r8161_closed
  · subst row; exact c9r8162_closed
  · subst row; exact c9r8163_closed
  · subst row; exact c9r8164_closed
  · subst row; exact c9r8165_closed
  · subst row; exact c9r8166_closed
  · subst row; exact c9r8167_closed
theorem C9R08160G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8168_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r8168targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r8168choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8168targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r8168choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8168targets, c9r8168choice, ?_, checked⟩
    intro S h
    simp only [c9r8168targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 11 _ (by rfl)
  have c9r8169_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r8169targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r8169choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8169targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r8169choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8169targets, c9r8169choice, ?_, checked⟩
    intro S h
    simp only [c9r8169targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 14 _ (by rfl)
  have c9r8170_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r8170targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r8170choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8170targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r8170choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8170targets, c9r8170choice, ?_, checked⟩
    intro S h
    simp only [c9r8170targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 17 _ (by rfl)
  have c9r8171_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r8171targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r8171choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8171targets [(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)] c9r8171choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8171targets, c9r8171choice, ?_, checked⟩
    intro S h
    simp only [c9r8171targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 23 _ (by rfl)
  have c9r8172_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r8172targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r8172choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8172targets [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r8172choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8172targets, c9r8172choice, ?_, checked⟩
    intro S h
    simp only [c9r8172targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 29 _ (by rfl)
  have c9r8173_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r8173targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r8173choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8173targets [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)] c9r8173choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8173targets, c9r8173choice, ?_, checked⟩
    intro S h
    simp only [c9r8173targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 2 _ (by rfl)
  have c9r8174_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c9r8174targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c9r8174choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8174targets [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)] c9r8174choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8174targets, c9r8174choice, ?_, checked⟩
    intro S h
    simp only [c9r8174targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 4 _ (by rfl)
  have c9r8175_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c9r8175targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c9r8175choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8175targets [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)] c9r8175choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8175targets, c9r8175choice, ?_, checked⟩
    intro S h
    simp only [c9r8175targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8168_closed
  · subst row; exact c9r8169_closed
  · subst row; exact c9r8170_closed
  · subst row; exact c9r8171_closed
  · subst row; exact c9r8172_closed
  · subst row; exact c9r8173_closed
  · subst row; exact c9r8174_closed
  · subst row; exact c9r8175_closed
theorem C9R08160G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8176_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)] := by
    let c9r8176targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)]]
    let c9r8176choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8176targets [(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)] c9r8176choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8176targets, c9r8176choice, ?_, checked⟩
    intro S h
    simp only [c9r8176targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 10 _ (by rfl)
  have c9r8177_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r8177targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r8177choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8177targets [(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r8177choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8177targets, c9r8177choice, ?_, checked⟩
    intro S h
    simp only [c9r8177targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 18 _ (by rfl)
  have c9r8178_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r8178targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r8178choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8178targets [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r8178choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8178targets, c9r8178choice, ?_, checked⟩
    intro S h
    simp only [c9r8178targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 25 _ (by rfl)
  have c9r8179_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r8179targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r8179choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8179targets [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r8179choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8179targets, c9r8179choice, ?_, checked⟩
    intro S h
    simp only [c9r8179targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 28 _ (by rfl)
  have c9r8180_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r8180targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r8180choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8180targets [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r8180choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8180targets, c9r8180choice, ?_, checked⟩
    intro S h
    simp only [c9r8180targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 30 _ (by rfl)
  have c9r8181_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r8181targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r8181choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8181targets [(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r8181choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8181targets, c9r8181choice, ?_, checked⟩
    intro S h
    simp only [c9r8181targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 0 _ (by rfl)
  have c9r8182_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r8182targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r8182choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8182targets [(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)] c9r8182choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8182targets, c9r8182choice, ?_, checked⟩
    intro S h
    simp only [c9r8182targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 5 _ (by rfl)
  have c9r8183_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r8183targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r8183choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8183targets [(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)] c9r8183choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8183targets, c9r8183choice, ?_, checked⟩
    intro S h
    simp only [c9r8183targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8176_closed
  · subst row; exact c9r8177_closed
  · subst row; exact c9r8178_closed
  · subst row; exact c9r8179_closed
  · subst row; exact c9r8180_closed
  · subst row; exact c9r8181_closed
  · subst row; exact c9r8182_closed
  · subst row; exact c9r8183_closed
theorem C9R08160G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8184_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r8184targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r8184choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8184targets [(0,2),(1,2),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)] c9r8184choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8184targets, c9r8184choice, ?_, checked⟩
    intro S h
    simp only [c9r8184targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 19 _ (by rfl)
  have c9r8185_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r8185targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(1,3),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,1),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,3),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r8185choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8185targets [(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r8185choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8185targets, c9r8185choice, ?_, checked⟩
    intro S h
    simp only [c9r8185targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 29 _ (by rfl)
  have c9r8186_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r8186targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,2),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r8186choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8186targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] c9r8186choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8186targets, c9r8186choice, ?_, checked⟩
    intro S h
    simp only [c9r8186targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 7 _ (by rfl)
  have c9r8187_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)] := by
    let c9r8187targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(5,0)]]
    let c9r8187choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8187targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)] c9r8187choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8187targets, c9r8187choice, ?_, checked⟩
    intro S h
    simp only [c9r8187targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 12 _ (by rfl)
  have c9r8188_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)] := by
    let c9r8188targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)]]
    let c9r8188choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8188targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)] c9r8188choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8188targets, c9r8188choice, ?_, checked⟩
    intro S h
    simp only [c9r8188targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 16 _ (by rfl)
  have c9r8189_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r8189targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r8189choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8189targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)] c9r8189choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8189targets, c9r8189choice, ?_, checked⟩
    intro S h
    simp only [c9r8189targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 19 _ (by rfl)
  have c9r8190_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r8190targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r8190choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8190targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)] c9r8190choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8190targets, c9r8190choice, ?_, checked⟩
    intro S h
    simp only [c9r8190targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 21 _ (by rfl)
  have c9r8191_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r8191targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,4)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r8191choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8191targets [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)] c9r8191choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8191targets, c9r8191choice, ?_, checked⟩
    intro S h
    simp only [c9r8191targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8184_closed
  · subst row; exact c9r8185_closed
  · subst row; exact c9r8186_closed
  · subst row; exact c9r8187_closed
  · subst row; exact c9r8188_closed
  · subst row; exact c9r8189_closed
  · subst row; exact c9r8190_closed
  · subst row; exact c9r8191_closed
theorem C9R08160_closed (row : List GridPoint) (h : FamilyMember row F9B003L63) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L63, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08160G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08160G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08160G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08160G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08160G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08160G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08160G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08160G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08160G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08160G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08160G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08160G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08160G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08160G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08160G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08160G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08160G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08160G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08160G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08160G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08160G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08160G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08160G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08160G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08160G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08160G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08160G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08160G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08160G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08160G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08160G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08160G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
