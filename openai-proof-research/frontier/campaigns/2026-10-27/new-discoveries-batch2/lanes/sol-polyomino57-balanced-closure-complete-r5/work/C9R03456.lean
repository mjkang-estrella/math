import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03456G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3456_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r3456targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r3456choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3456targets [(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r3456choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3456targets, c9r3456choice, ?_, checked⟩
    intro S h
    simp only [c9r3456targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 13 _ (by rfl)
  have c9r3457_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r3457targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r3457choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3457targets [(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r3457choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3457targets, c9r3457choice, ?_, checked⟩
    intro S h
    simp only [c9r3457targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 27 _ (by rfl)
  have c9r3458_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r3458targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r3458choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c9r3458targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] c9r3458choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3458targets, c9r3458choice, ?_, checked⟩
    intro S h
    simp only [c9r3458targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 4 _ (by rfl)
  have c9r3459_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)] := by
    let c9r3459targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(4,0)]]
    let c9r3459choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3459targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)] c9r3459choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3459targets, c9r3459choice, ?_, checked⟩
    intro S h
    simp only [c9r3459targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 10 _ (by rfl)
  have c9r3460_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)] := by
    let c9r3460targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)]]
    let c9r3460choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3460targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)] c9r3460choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3460targets, c9r3460choice, ?_, checked⟩
    intro S h
    simp only [c9r3460targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 15 _ (by rfl)
  have c9r3461_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)] := by
    let c9r3461targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)]]
    let c9r3461choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3461targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)] c9r3461choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3461targets, c9r3461choice, ?_, checked⟩
    intro S h
    simp only [c9r3461targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 19 _ (by rfl)
  have c9r3462_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)] := by
    let c9r3462targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c9r3462choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3462targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)] c9r3462choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3462targets, c9r3462choice, ?_, checked⟩
    intro S h
    simp only [c9r3462targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 22 _ (by rfl)
  have c9r3463_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)] := by
    let c9r3463targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c9r3463choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3463targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)] c9r3463choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3463targets, c9r3463choice, ?_, checked⟩
    intro S h
    simp only [c9r3463targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3456_closed
  · subst row; exact c9r3457_closed
  · subst row; exact c9r3458_closed
  · subst row; exact c9r3459_closed
  · subst row; exact c9r3460_closed
  · subst row; exact c9r3461_closed
  · subst row; exact c9r3462_closed
  · subst row; exact c9r3463_closed
theorem C9R03456G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3464_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r3464targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r3464choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3464targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] c9r3464choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3464targets, c9r3464choice, ?_, checked⟩
    intro S h
    simp only [c9r3464targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 26 _ (by rfl)
  have c9r3465_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] := by
    let c9r3465targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)]]
    let c9r3465choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3465targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] c9r3465choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3465targets, c9r3465choice, ?_, checked⟩
    intro S h
    simp only [c9r3465targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 31 _ (by rfl)
  have c9r3466_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)] := by
    let c9r3466targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,2)]]
    let c9r3466choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3466targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)] c9r3466choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3466targets, c9r3466choice, ?_, checked⟩
    intro S h
    simp only [c9r3466targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 3 _ (by rfl)
  have c9r3467_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)] := by
    let c9r3467targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(4,3)]]
    let c9r3467choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3467targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)] c9r3467choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3467targets, c9r3467choice, ?_, checked⟩
    intro S h
    simp only [c9r3467targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 6 _ (by rfl)
  have c9r3468_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)] := by
    let c9r3468targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,4)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(4,4)]]
    let c9r3468choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3468targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)] c9r3468choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3468targets, c9r3468choice, ?_, checked⟩
    intro S h
    simp only [c9r3468targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 9 _ (by rfl)
  have c9r3469_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)] := by
    let c9r3469targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0),(5,0)]]
    let c9r3469choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3469targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)] c9r3469choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3469targets, c9r3469choice, ?_, checked⟩
    intro S h
    simp only [c9r3469targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 11 _ (by rfl)
  have c9r3470_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)] := by
    let c9r3470targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)]]
    let c9r3470choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3470targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)] c9r3470choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3470targets, c9r3470choice, ?_, checked⟩
    intro S h
    simp only [c9r3470targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 15 _ (by rfl)
  have c9r3471_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)] := by
    let c9r3471targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)]]
    let c9r3471choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3471targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)] c9r3471choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3471targets, c9r3471choice, ?_, checked⟩
    intro S h
    simp only [c9r3471targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 18 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3464_closed
  · subst row; exact c9r3465_closed
  · subst row; exact c9r3466_closed
  · subst row; exact c9r3467_closed
  · subst row; exact c9r3468_closed
  · subst row; exact c9r3469_closed
  · subst row; exact c9r3470_closed
  · subst row; exact c9r3471_closed
theorem C9R03456G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3472_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)] := by
    let c9r3472targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,4)]]
    let c9r3472choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3472targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)] c9r3472choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3472targets, c9r3472choice, ?_, checked⟩
    intro S h
    simp only [c9r3472targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 21 _ (by rfl)
  have c9r3473_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)] := by
    let c9r3473targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,1)]]
    let c9r3473choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3473targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)] c9r3473choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3473targets, c9r3473choice, ?_, checked⟩
    intro S h
    simp only [c9r3473targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 24 _ (by rfl)
  have c9r3474_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)] := by
    let c9r3474targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)]]
    let c9r3474choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3474targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)] c9r3474choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3474targets, c9r3474choice, ?_, checked⟩
    intro S h
    simp only [c9r3474targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 27 _ (by rfl)
  have c9r3475_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)] := by
    let c9r3475targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)]]
    let c9r3475choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3475targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)] c9r3475choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3475targets, c9r3475choice, ?_, checked⟩
    intro S h
    simp only [c9r3475targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 30 _ (by rfl)
  have c9r3476_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)] := by
    let c9r3476targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)]]
    let c9r3476choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3476targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)] c9r3476choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3476targets, c9r3476choice, ?_, checked⟩
    intro S h
    simp only [c9r3476targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 1 _ (by rfl)
  have c9r3477_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)] := by
    let c9r3477targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]]
    let c9r3477choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3477targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)] c9r3477choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3477targets, c9r3477choice, ?_, checked⟩
    intro S h
    simp only [c9r3477targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 4 _ (by rfl)
  have c9r3478_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)] := by
    let c9r3478targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)]]
    let c9r3478choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3478targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)] c9r3478choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3478targets, c9r3478choice, ?_, checked⟩
    intro S h
    simp only [c9r3478targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 7 _ (by rfl)
  have c9r3479_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)] := by
    let c9r3479targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)]]
    let c9r3479choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3479targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)] c9r3479choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3479targets, c9r3479choice, ?_, checked⟩
    intro S h
    simp only [c9r3479targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3472_closed
  · subst row; exact c9r3473_closed
  · subst row; exact c9r3474_closed
  · subst row; exact c9r3475_closed
  · subst row; exact c9r3476_closed
  · subst row; exact c9r3477_closed
  · subst row; exact c9r3478_closed
  · subst row; exact c9r3479_closed
theorem C9R03456G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3480_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)] := by
    let c9r3480targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)]]
    let c9r3480choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3480targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)] c9r3480choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3480targets, c9r3480choice, ?_, checked⟩
    intro S h
    simp only [c9r3480targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 13 _ (by rfl)
  have c9r3481_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r3481targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r3481choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3481targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r3481choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3481targets, c9r3481choice, ?_, checked⟩
    intro S h
    simp only [c9r3481targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 18 _ (by rfl)
  have c9r3482_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] := by
    let c9r3482targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)]]
    let c9r3482choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3482targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] c9r3482choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3482targets, c9r3482choice, ?_, checked⟩
    intro S h
    simp only [c9r3482targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 22 _ (by rfl)
  have c9r3483_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] := by
    let c9r3483targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)]]
    let c9r3483choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3483targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] c9r3483choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3483targets, c9r3483choice, ?_, checked⟩
    intro S h
    simp only [c9r3483targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 24 _ (by rfl)
  have c9r3484_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] := by
    let c9r3484targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)]]
    let c9r3484choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3484targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] c9r3484choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3484targets, c9r3484choice, ?_, checked⟩
    intro S h
    simp only [c9r3484targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 26 _ (by rfl)
  have c9r3485_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)] := by
    let c9r3485targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,3)]]
    let c9r3485choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3485targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)] c9r3485choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3485targets, c9r3485choice, ?_, checked⟩
    intro S h
    simp only [c9r3485targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 30 _ (by rfl)
  have c9r3486_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)] := by
    let c9r3486targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(5,0)]]
    let c9r3486choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3486targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)] c9r3486choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3486targets, c9r3486choice, ?_, checked⟩
    intro S h
    simp only [c9r3486targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 1 _ (by rfl)
  have c9r3487_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)] := by
    let c9r3487targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2),(5,2)]]
    let c9r3487choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3487targets [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)] c9r3487choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3487targets, c9r3487choice, ?_, checked⟩
    intro S h
    simp only [c9r3487targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3480_closed
  · subst row; exact c9r3481_closed
  · subst row; exact c9r3482_closed
  · subst row; exact c9r3483_closed
  · subst row; exact c9r3484_closed
  · subst row; exact c9r3485_closed
  · subst row; exact c9r3486_closed
  · subst row; exact c9r3487_closed
theorem C9R03456_closed (row : List GridPoint) (h : FamilyMember row F9B001L44) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L44, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03456G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03456G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03456G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03456G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03456G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03456G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03456G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03456G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03456G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03456G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03456G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03456G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03456G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03456G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03456G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03456G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03456G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03456G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03456G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03456G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03456G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03456G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03456G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03456G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03456G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03456G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03456G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03456G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03456G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03456G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03456G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03456G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
