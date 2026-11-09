import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08224G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8224_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r8224targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r8224choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8224targets [(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r8224choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8224targets, c9r8224choice, ?_, checked⟩
    intro S h
    simp only [c9r8224targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 31 _ (by rfl)
  have c9r8225_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r8225targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,3),(3,1),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r8225choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8225targets [(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r8225choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8225targets, c9r8225choice, ?_, checked⟩
    intro S h
    simp only [c9r8225targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 2 _ (by rfl)
  have c9r8226_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r8226targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r8226choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8226targets [(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r8226choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8226targets, c9r8226choice, ?_, checked⟩
    intro S h
    simp only [c9r8226targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 4 _ (by rfl)
  have c9r8227_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r8227targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r8227choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8227targets [(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r8227choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8227targets, c9r8227choice, ?_, checked⟩
    intro S h
    simp only [c9r8227targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 6 _ (by rfl)
  have c9r8228_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)] := by
    let c9r8228targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,4)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,1)]]
    let c9r8228choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8228targets [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)] c9r8228choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8228targets, c9r8228choice, ?_, checked⟩
    intro S h
    simp only [c9r8228targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 13 _ (by rfl)
  have c9r8229_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r8229targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r8229choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8229targets [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r8229choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8229targets, c9r8229choice, ?_, checked⟩
    intro S h
    simp only [c9r8229targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 18 _ (by rfl)
  have c9r8230_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)] := by
    let c9r8230targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,3)],[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,4)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,3)]]
    let c9r8230choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8230targets [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)] c9r8230choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8230targets, c9r8230choice, ?_, checked⟩
    intro S h
    simp only [c9r8230targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 22 _ (by rfl)
  have c9r8231_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)] := by
    let c9r8231targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(6,0)]]
    let c9r8231choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8231targets [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)] c9r8231choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8231targets, c9r8231choice, ?_, checked⟩
    intro S h
    simp only [c9r8231targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8224_closed
  · subst row; exact c9r8225_closed
  · subst row; exact c9r8226_closed
  · subst row; exact c9r8227_closed
  · subst row; exact c9r8228_closed
  · subst row; exact c9r8229_closed
  · subst row; exact c9r8230_closed
  · subst row; exact c9r8231_closed
theorem C9R08224G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8232_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)] := by
    let c9r8232targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(6,1)]]
    let c9r8232choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8232targets [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)] c9r8232choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8232targets, c9r8232choice, ?_, checked⟩
    intro S h
    simp only [c9r8232targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 26 _ (by rfl)
  have c9r8233_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)] := by
    let c9r8233targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,1)]]
    let c9r8233choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8233targets [(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)] c9r8233choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8233targets, c9r8233choice, ?_, checked⟩
    intro S h
    simp only [c9r8233targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 31 _ (by rfl)
  have c9r8234_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r8234targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r8234choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8234targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r8234choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8234targets, c9r8234choice, ?_, checked⟩
    intro S h
    simp only [c9r8234targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 6 _ (by rfl)
  have c9r8235_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r8235targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r8235choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8235targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r8235choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8235targets, c9r8235choice, ?_, checked⟩
    intro S h
    simp only [c9r8235targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 9 _ (by rfl)
  have c9r8236_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r8236targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r8236choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8236targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r8236choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8236targets, c9r8236choice, ?_, checked⟩
    intro S h
    simp only [c9r8236targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 11 _ (by rfl)
  have c9r8237_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r8237targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r8237choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8237targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r8237choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8237targets, c9r8237choice, ?_, checked⟩
    intro S h
    simp only [c9r8237targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 13 _ (by rfl)
  have c9r8238_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)] := by
    let c9r8238targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,1)]]
    let c9r8238choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8238targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)] c9r8238choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8238targets, c9r8238choice, ?_, checked⟩
    intro S h
    simp only [c9r8238targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 16 _ (by rfl)
  have c9r8239_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)] := by
    let c9r8239targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0),(7,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(6,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0),(7,0)]]
    let c9r8239choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8239targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)] c9r8239choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8239targets, c9r8239choice, ?_, checked⟩
    intro S h
    simp only [c9r8239targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 18 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8232_closed
  · subst row; exact c9r8233_closed
  · subst row; exact c9r8234_closed
  · subst row; exact c9r8235_closed
  · subst row; exact c9r8236_closed
  · subst row; exact c9r8237_closed
  · subst row; exact c9r8238_closed
  · subst row; exact c9r8239_closed
theorem C9R08224G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8240_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)] := by
    let c9r8240targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,2)]]
    let c9r8240choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8240targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)] c9r8240choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8240targets, c9r8240choice, ?_, checked⟩
    intro S h
    simp only [c9r8240targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 21 _ (by rfl)
  have c9r8241_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)] := by
    let c9r8241targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(6,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c9r8241choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8241targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)] c9r8241choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8241targets, c9r8241choice, ?_, checked⟩
    intro S h
    simp only [c9r8241targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 24 _ (by rfl)
  have c9r8242_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r8242targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r8242choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8242targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)] c9r8242choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8242targets, c9r8242choice, ?_, checked⟩
    intro S h
    simp only [c9r8242targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 29 _ (by rfl)
  have c9r8243_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)] := by
    let c9r8243targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c9r8243choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8243targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)] c9r8243choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8243targets, c9r8243choice, ?_, checked⟩
    intro S h
    simp only [c9r8243targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 2 _ (by rfl)
  have c9r8244_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)] := by
    let c9r8244targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1),(7,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c9r8244choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8244targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)] c9r8244choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8244targets, c9r8244choice, ?_, checked⟩
    intro S h
    simp only [c9r8244targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 4 _ (by rfl)
  have c9r8245_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)] := by
    let c9r8245targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c9r8245choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8245targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)] c9r8245choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8245targets, c9r8245choice, ?_, checked⟩
    intro S h
    simp only [c9r8245targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 6 _ (by rfl)
  have c9r8246_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)] := by
    let c9r8246targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1),(7,0),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1),(7,1)]]
    let c9r8246choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8246targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)] c9r8246choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8246targets, c9r8246choice, ?_, checked⟩
    intro S h
    simp only [c9r8246targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 10 _ (by rfl)
  have c9r8247_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r8247targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r8247choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8247targets [(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)] c9r8247choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8247targets, c9r8247choice, ?_, checked⟩
    intro S h
    simp only [c9r8247targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8240_closed
  · subst row; exact c9r8241_closed
  · subst row; exact c9r8242_closed
  · subst row; exact c9r8243_closed
  · subst row; exact c9r8244_closed
  · subst row; exact c9r8245_closed
  · subst row; exact c9r8246_closed
  · subst row; exact c9r8247_closed
theorem C9R08224G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8248_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)] := by
    let c9r8248targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,4)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,2)]]
    let c9r8248choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8248targets [(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)] c9r8248choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8248targets, c9r8248choice, ?_, checked⟩
    intro S h
    simp only [c9r8248targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 24 _ (by rfl)
  have c9r8249_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r8249targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r8249choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8249targets [(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)] c9r8249choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8249targets, c9r8249choice, ?_, checked⟩
    intro S h
    simp only [c9r8249targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 31 _ (by rfl)
  have c9r8250_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r8250targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,3),(3,3),(3,4),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r8250choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8250targets [(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)] c9r8250choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8250targets, c9r8250choice, ?_, checked⟩
    intro S h
    simp only [c9r8250targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 2 _ (by rfl)
  have c9r8251_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r8251targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r8251choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8251targets [(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)] c9r8251choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8251targets, c9r8251choice, ?_, checked⟩
    intro S h
    simp only [c9r8251targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 4 _ (by rfl)
  have c9r8252_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r8252targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r8252choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8252targets [(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)] c9r8252choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8252targets, c9r8252choice, ?_, checked⟩
    intro S h
    simp only [c9r8252targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 6 _ (by rfl)
  have c9r8253_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r8253targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r8253choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8253targets [(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)] c9r8253choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8253targets, c9r8253choice, ?_, checked⟩
    intro S h
    simp only [c9r8253targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 11 _ (by rfl)
  have c9r8254_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r8254targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r8254choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8254targets [(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)] c9r8254choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8254targets, c9r8254choice, ?_, checked⟩
    intro S h
    simp only [c9r8254targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 17 _ (by rfl)
  have c9r8255_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)] := by
    let c9r8255targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(5,4)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,2),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,4)]]
    let c9r8255choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8255targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)] c9r8255choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8255targets, c9r8255choice, ?_, checked⟩
    intro S h
    simp only [c9r8255targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8248_closed
  · subst row; exact c9r8249_closed
  · subst row; exact c9r8250_closed
  · subst row; exact c9r8251_closed
  · subst row; exact c9r8252_closed
  · subst row; exact c9r8253_closed
  · subst row; exact c9r8254_closed
  · subst row; exact c9r8255_closed
theorem C9R08224_closed (row : List GridPoint) (h : FamilyMember row F9B004L1) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L1, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08224G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08224G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08224G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08224G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08224G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08224G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08224G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08224G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08224G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08224G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08224G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08224G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08224G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08224G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08224G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08224G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08224G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08224G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08224G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08224G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08224G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08224G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08224G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08224G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08224G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08224G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08224G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08224G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08224G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08224G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08224G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08224G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
