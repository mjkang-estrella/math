import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R04256G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4256_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] := by
    let c9r4256targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)]]
    let c9r4256choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4256targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] c9r4256choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4256targets, c9r4256choice, ?_, checked⟩
    intro S h
    simp only [c9r4256targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 12 _ (by rfl)
  have c9r4257_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] := by
    let c9r4257targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]
    let c9r4257choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4257targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] c9r4257choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4257targets, c9r4257choice, ?_, checked⟩
    intro S h
    simp only [c9r4257targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 15 _ (by rfl)
  have c9r4258_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] := by
    let c9r4258targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c9r4258choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4258targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] c9r4258choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4258targets, c9r4258choice, ?_, checked⟩
    intro S h
    simp only [c9r4258targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 19 _ (by rfl)
  have c9r4259_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] := by
    let c9r4259targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c9r4259choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4259targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] c9r4259choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4259targets, c9r4259choice, ?_, checked⟩
    intro S h
    simp only [c9r4259targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 22 _ (by rfl)
  have c9r4260_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] := by
    let c9r4260targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c9r4260choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4260targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] c9r4260choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4260targets, c9r4260choice, ?_, checked⟩
    intro S h
    simp only [c9r4260targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 24 _ (by rfl)
  have c9r4261_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] := by
    let c9r4261targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c9r4261choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4261targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] c9r4261choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4261targets, c9r4261choice, ?_, checked⟩
    intro S h
    simp only [c9r4261targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
  have c9r4262_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] := by
    let c9r4262targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c9r4262choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4262targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] c9r4262choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4262targets, c9r4262choice, ?_, checked⟩
    intro S h
    simp only [c9r4262targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 31 _ (by rfl)
  have c9r4263_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] := by
    let c9r4263targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)]]
    let c9r4263choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4263targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] c9r4263choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4263targets, c9r4263choice, ?_, checked⟩
    intro S h
    simp only [c9r4263targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4256_closed
  · subst row; exact c9r4257_closed
  · subst row; exact c9r4258_closed
  · subst row; exact c9r4259_closed
  · subst row; exact c9r4260_closed
  · subst row; exact c9r4261_closed
  · subst row; exact c9r4262_closed
  · subst row; exact c9r4263_closed
theorem C9R04256G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4264_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] := by
    let c9r4264targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c9r4264choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4264targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)] c9r4264choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4264targets, c9r4264choice, ?_, checked⟩
    intro S h
    simp only [c9r4264targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 9 _ (by rfl)
  have c9r4265_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r4265targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r4265choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4265targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)] c9r4265choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4265targets, c9r4265choice, ?_, checked⟩
    intro S h
    simp only [c9r4265targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 15 _ (by rfl)
  have c9r4266_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r4266targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r4266choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4266targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)] c9r4266choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4266targets, c9r4266choice, ?_, checked⟩
    intro S h
    simp only [c9r4266targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
  have c9r4267_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r4267targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r4267choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))))))
    have checked : successorFastRowCheck c9r4267targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)] c9r4267choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4267targets, c9r4267choice, ?_, checked⟩
    intro S h
    simp only [c9r4267targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
  have c9r4268_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r4268targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r4268choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4268targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)] c9r4268choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4268targets, c9r4268choice, ?_, checked⟩
    intro S h
    simp only [c9r4268targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 22 _ (by rfl)
  have c9r4269_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] := by
    let c9r4269targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c9r4269choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4269targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)] c9r4269choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4269targets, c9r4269choice, ?_, checked⟩
    intro S h
    simp only [c9r4269targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 25 _ (by rfl)
  have c9r4270_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] := by
    let c9r4270targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c9r4270choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4270targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)] c9r4270choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4270targets, c9r4270choice, ?_, checked⟩
    intro S h
    simp only [c9r4270targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 27 _ (by rfl)
  have c9r4271_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] := by
    let c9r4271targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c9r4271choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4271targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)] c9r4271choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4271targets, c9r4271choice, ?_, checked⟩
    intro S h
    simp only [c9r4271targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4264_closed
  · subst row; exact c9r4265_closed
  · subst row; exact c9r4266_closed
  · subst row; exact c9r4267_closed
  · subst row; exact c9r4268_closed
  · subst row; exact c9r4269_closed
  · subst row; exact c9r4270_closed
  · subst row; exact c9r4271_closed
theorem C9R04256G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4272_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] := by
    let c9r4272targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c9r4272choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4272targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)] c9r4272choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4272targets, c9r4272choice, ?_, checked⟩
    intro S h
    simp only [c9r4272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 1 _ (by rfl)
  have c9r4273_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)] := by
    let c9r4273targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)]]
    let c9r4273choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4273targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)] c9r4273choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4273targets, c9r4273choice, ?_, checked⟩
    intro S h
    simp only [c9r4273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 6 _ (by rfl)
  have c9r4274_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)] := by
    let c9r4274targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)]]
    let c9r4274choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4274targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)] c9r4274choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4274targets, c9r4274choice, ?_, checked⟩
    intro S h
    simp only [c9r4274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 10 _ (by rfl)
  have c9r4275_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)] := by
    let c9r4275targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)]]
    let c9r4275choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4275targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)] c9r4275choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4275targets, c9r4275choice, ?_, checked⟩
    intro S h
    simp only [c9r4275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
  have c9r4276_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)] := by
    let c9r4276targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3)]]
    let c9r4276choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4276targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)] c9r4276choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4276targets, c9r4276choice, ?_, checked⟩
    intro S h
    simp only [c9r4276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 15 _ (by rfl)
  have c9r4277_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)] := by
    let c9r4277targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1)]]
    let c9r4277choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4277targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)] c9r4277choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4277targets, c9r4277choice, ?_, checked⟩
    intro S h
    simp only [c9r4277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 18 _ (by rfl)
  have c9r4278_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)] := by
    let c9r4278targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)]]
    let c9r4278choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4278targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)] c9r4278choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4278targets, c9r4278choice, ?_, checked⟩
    intro S h
    simp only [c9r4278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 21 _ (by rfl)
  have c9r4279_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)] := by
    let c9r4279targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)]]
    let c9r4279choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4279targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)] c9r4279choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4279targets, c9r4279choice, ?_, checked⟩
    intro S h
    simp only [c9r4279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4272_closed
  · subst row; exact c9r4273_closed
  · subst row; exact c9r4274_closed
  · subst row; exact c9r4275_closed
  · subst row; exact c9r4276_closed
  · subst row; exact c9r4277_closed
  · subst row; exact c9r4278_closed
  · subst row; exact c9r4279_closed
theorem C9R04256G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4280_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)] := by
    let c9r4280targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)]]
    let c9r4280choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4280targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)] c9r4280choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4280targets, c9r4280choice, ?_, checked⟩
    intro S h
    simp only [c9r4280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 26 _ (by rfl)
  have c9r4281_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)] := by
    let c9r4281targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)]]
    let c9r4281choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4281targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)] c9r4281choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4281targets, c9r4281choice, ?_, checked⟩
    intro S h
    simp only [c9r4281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 29 _ (by rfl)
  have c9r4282_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)] := by
    let c9r4282targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)]]
    let c9r4282choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4282targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)] c9r4282choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4282targets, c9r4282choice, ?_, checked⟩
    intro S h
    simp only [c9r4282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 0 _ (by rfl)
  have c9r4283_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)] := by
    let c9r4283targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)]]
    let c9r4283choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4283targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)] c9r4283choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4283targets, c9r4283choice, ?_, checked⟩
    intro S h
    simp only [c9r4283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 4 _ (by rfl)
  have c9r4284_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)] := by
    let c9r4284targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)]]
    let c9r4284choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4284targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)] c9r4284choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4284targets, c9r4284choice, ?_, checked⟩
    intro S h
    simp only [c9r4284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 6 _ (by rfl)
  have c9r4285_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)] := by
    let c9r4285targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)]]
    let c9r4285choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4285targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)] c9r4285choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4285targets, c9r4285choice, ?_, checked⟩
    intro S h
    simp only [c9r4285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 8 _ (by rfl)
  have c9r4286_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)] := by
    let c9r4286targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)]]
    let c9r4286choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4286targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)] c9r4286choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4286targets, c9r4286choice, ?_, checked⟩
    intro S h
    simp only [c9r4286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 11 _ (by rfl)
  have c9r4287_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)] := by
    let c9r4287targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)]]
    let c9r4287choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4287targets [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)] c9r4287choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4287targets, c9r4287choice, ?_, checked⟩
    intro S h
    simp only [c9r4287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4280_closed
  · subst row; exact c9r4281_closed
  · subst row; exact c9r4282_closed
  · subst row; exact c9r4283_closed
  · subst row; exact c9r4284_closed
  · subst row; exact c9r4285_closed
  · subst row; exact c9r4286_closed
  · subst row; exact c9r4287_closed
theorem C9R04256_closed (row : List GridPoint) (h : FamilyMember row F9B002L5) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L5, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R04256G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04256G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04256G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04256G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04256G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04256G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04256G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04256G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04256G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04256G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04256G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04256G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04256G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04256G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04256G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04256G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04256G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04256G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04256G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04256G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04256G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04256G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04256G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04256G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04256G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04256G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04256G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04256G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04256G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04256G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04256G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04256G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
