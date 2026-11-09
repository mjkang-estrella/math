import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R05376G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5376_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r5376targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r5376choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5376targets [(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r5376choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5376targets, c9r5376choice, ?_, checked⟩
    intro S h
    simp only [c9r5376targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 11 _ (by rfl)
  have c9r5377_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r5377targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,5),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,5),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,6),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,3),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r5377choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5377targets [(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r5377choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5377targets, c9r5377choice, ?_, checked⟩
    intro S h
    simp only [c9r5377targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 22 _ (by rfl)
  have c9r5378_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r5378targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r5378choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5378targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r5378choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5378targets, c9r5378choice, ?_, checked⟩
    intro S h
    simp only [c9r5378targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 30 _ (by rfl)
  have c9r5379_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] := by
    let c9r5379targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c9r5379choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5379targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] c9r5379choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5379targets, c9r5379choice, ?_, checked⟩
    intro S h
    simp only [c9r5379targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 3 _ (by rfl)
  have c9r5380_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r5380targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r5380choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5380targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r5380choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5380targets, c9r5380choice, ?_, checked⟩
    intro S h
    simp only [c9r5380targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 7 _ (by rfl)
  have c9r5381_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r5381targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r5381choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5381targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r5381choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5381targets, c9r5381choice, ?_, checked⟩
    intro S h
    simp only [c9r5381targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 10 _ (by rfl)
  have c9r5382_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r5382targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r5382choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5382targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r5382choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5382targets, c9r5382choice, ?_, checked⟩
    intro S h
    simp only [c9r5382targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 12 _ (by rfl)
  have c9r5383_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r5383targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r5383choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5383targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r5383choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5383targets, c9r5383choice, ?_, checked⟩
    intro S h
    simp only [c9r5383targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5376_closed
  · subst row; exact c9r5377_closed
  · subst row; exact c9r5378_closed
  · subst row; exact c9r5379_closed
  · subst row; exact c9r5380_closed
  · subst row; exact c9r5381_closed
  · subst row; exact c9r5382_closed
  · subst row; exact c9r5383_closed
theorem C9R05376G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5384_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r5384targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r5384choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5384targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r5384choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5384targets, c9r5384choice, ?_, checked⟩
    intro S h
    simp only [c9r5384targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 18 _ (by rfl)
  have c9r5385_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] := by
    let c9r5385targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)]]
    let c9r5385choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5385targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] c9r5385choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5385targets, c9r5385choice, ?_, checked⟩
    intro S h
    simp only [c9r5385targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 21 _ (by rfl)
  have c9r5386_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] := by
    let c9r5386targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)]]
    let c9r5386choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5386targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] c9r5386choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5386targets, c9r5386choice, ?_, checked⟩
    intro S h
    simp only [c9r5386targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 24 _ (by rfl)
  have c9r5387_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] := by
    let c9r5387targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)]]
    let c9r5387choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5387targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] c9r5387choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5387targets, c9r5387choice, ?_, checked⟩
    intro S h
    simp only [c9r5387targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 26 _ (by rfl)
  have c9r5388_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)] := by
    let c9r5388targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c9r5388choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5388targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)] c9r5388choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5388targets, c9r5388choice, ?_, checked⟩
    intro S h
    simp only [c9r5388targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 29 _ (by rfl)
  have c9r5389_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)] := by
    let c9r5389targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)]]
    let c9r5389choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5389targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)] c9r5389choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5389targets, c9r5389choice, ?_, checked⟩
    intro S h
    simp only [c9r5389targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 0 _ (by rfl)
  have c9r5390_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)] := by
    let c9r5390targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)]]
    let c9r5390choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5390targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)] c9r5390choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5390targets, c9r5390choice, ?_, checked⟩
    intro S h
    simp only [c9r5390targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 3 _ (by rfl)
  have c9r5391_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)] := by
    let c9r5391targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c9r5391choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5391targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)] c9r5391choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5391targets, c9r5391choice, ?_, checked⟩
    intro S h
    simp only [c9r5391targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5384_closed
  · subst row; exact c9r5385_closed
  · subst row; exact c9r5386_closed
  · subst row; exact c9r5387_closed
  · subst row; exact c9r5388_closed
  · subst row; exact c9r5389_closed
  · subst row; exact c9r5390_closed
  · subst row; exact c9r5391_closed
theorem C9R05376G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5392_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)] := by
    let c9r5392targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c9r5392choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5392targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)] c9r5392choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5392targets, c9r5392choice, ?_, checked⟩
    intro S h
    simp only [c9r5392targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 9 _ (by rfl)
  have c9r5393_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)] := by
    let c9r5393targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c9r5393choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5393targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)] c9r5393choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5393targets, c9r5393choice, ?_, checked⟩
    intro S h
    simp only [c9r5393targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 12 _ (by rfl)
  have c9r5394_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)] := by
    let c9r5394targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c9r5394choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5394targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)] c9r5394choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5394targets, c9r5394choice, ?_, checked⟩
    intro S h
    simp only [c9r5394targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 15 _ (by rfl)
  have c9r5395_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r5395targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r5395choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5395targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)] c9r5395choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5395targets, c9r5395choice, ?_, checked⟩
    intro S h
    simp only [c9r5395targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 20 _ (by rfl)
  have c9r5396_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c9r5396targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c9r5396choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5396targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)] c9r5396choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5396targets, c9r5396choice, ?_, checked⟩
    intro S h
    simp only [c9r5396targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 22 _ (by rfl)
  have c9r5397_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c9r5397targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c9r5397choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5397targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)] c9r5397choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5397targets, c9r5397choice, ?_, checked⟩
    intro S h
    simp only [c9r5397targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 24 _ (by rfl)
  have c9r5398_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)] := by
    let c9r5398targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)]]
    let c9r5398choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5398targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)] c9r5398choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5398targets, c9r5398choice, ?_, checked⟩
    intro S h
    simp only [c9r5398targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 28 _ (by rfl)
  have c9r5399_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)] := by
    let c9r5399targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)]]
    let c9r5399choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5399targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)] c9r5399choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5399targets, c9r5399choice, ?_, checked⟩
    intro S h
    simp only [c9r5399targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5392_closed
  · subst row; exact c9r5393_closed
  · subst row; exact c9r5394_closed
  · subst row; exact c9r5395_closed
  · subst row; exact c9r5396_closed
  · subst row; exact c9r5397_closed
  · subst row; exact c9r5398_closed
  · subst row; exact c9r5399_closed
theorem C9R05376G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5400_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)] := by
    let c9r5400targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)]]
    let c9r5400choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5400targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)] c9r5400choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5400targets, c9r5400choice, ?_, checked⟩
    intro S h
    simp only [c9r5400targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 2 _ (by rfl)
  have c9r5401_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)] := by
    let c9r5401targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)]]
    let c9r5401choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5401targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)] c9r5401choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5401targets, c9r5401choice, ?_, checked⟩
    intro S h
    simp only [c9r5401targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 5 _ (by rfl)
  have c9r5402_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)] := by
    let c9r5402targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)]]
    let c9r5402choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5402targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)] c9r5402choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5402targets, c9r5402choice, ?_, checked⟩
    intro S h
    simp only [c9r5402targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 7 _ (by rfl)
  have c9r5403_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)] := by
    let c9r5403targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5403choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5403targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)] c9r5403choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5403targets, c9r5403choice, ?_, checked⟩
    intro S h
    simp only [c9r5403targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 11 _ (by rfl)
  have c9r5404_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)] := by
    let c9r5404targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c9r5404choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5404targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)] c9r5404choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5404targets, c9r5404choice, ?_, checked⟩
    intro S h
    simp only [c9r5404targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 14 _ (by rfl)
  have c9r5405_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c9r5405targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c9r5405choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5405targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)] c9r5405choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5405targets, c9r5405choice, ?_, checked⟩
    intro S h
    simp only [c9r5405targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 16 _ (by rfl)
  have c9r5406_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c9r5406targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c9r5406choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5406targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)] c9r5406choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5406targets, c9r5406choice, ?_, checked⟩
    intro S h
    simp only [c9r5406targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 19 _ (by rfl)
  have c9r5407_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c9r5407targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c9r5407choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5407targets [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)] c9r5407choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5407targets, c9r5407choice, ?_, checked⟩
    intro S h
    simp only [c9r5407targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5400_closed
  · subst row; exact c9r5401_closed
  · subst row; exact c9r5402_closed
  · subst row; exact c9r5403_closed
  · subst row; exact c9r5404_closed
  · subst row; exact c9r5405_closed
  · subst row; exact c9r5406_closed
  · subst row; exact c9r5407_closed
theorem C9R05376_closed (row : List GridPoint) (h : FamilyMember row F9B002L40) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L40, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R05376G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05376G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05376G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05376G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05376G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05376G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05376G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05376G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05376G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05376G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05376G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05376G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05376G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05376G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05376G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05376G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05376G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05376G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05376G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05376G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05376G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05376G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05376G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05376G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05376G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05376G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05376G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05376G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05376G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05376G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05376G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05376G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
