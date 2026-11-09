import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R09888G0 (row : List GridPoint) (h : row ∈ [[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9888_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r9888targets : Array (List GridPoint) := #[[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,4),(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(0,6),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,5)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r9888choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r9888targets [(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] c9r9888choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9888targets, c9r9888choice, ?_, checked⟩
    intro S h
    simp only [c9r9888targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 20 _ (by rfl)
  have c9r9889_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)] := by
    let c9r9889targets : Array (List GridPoint) := #[[(0,5),(1,5),(2,5),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1)],[(0,4),(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(0,6),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(1,2),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(1,3),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1)],[(0,6),(1,6),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,3)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,4)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,5)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(4,0)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(4,1)]]
    let c9r9889choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9889targets [(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)] c9r9889choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9889targets, c9r9889choice, ?_, checked⟩
    intro S h
    simp only [c9r9889targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 5 _ (by rfl)
  have c9r9890_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)] := by
    let c9r9890targets : Array (List GridPoint) := #[[(0,5),(1,5),(2,5),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2)],[(0,4),(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(0,6),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,3),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2)],[(0,6),(1,6),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,4)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,5)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,0)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,1)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,2)]]
    let c9r9890choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9890targets [(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)] c9r9890choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9890targets, c9r9890choice, ?_, checked⟩
    intro S h
    simp only [c9r9890targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 16 _ (by rfl)
  have c9r9891_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9891targets : Array (List GridPoint) := #[[(0,5),(1,5),(2,5),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2),(4,3)],[(0,4),(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(0,6),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,3),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,4),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,5),(1,6),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,5),(2,0),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,5),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,5),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,5),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3)],[(0,6),(1,6),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,5)],[(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9891choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9891targets [(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)] c9r9891choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9891targets, c9r9891choice, ?_, checked⟩
    intro S h
    simp only [c9r9891targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 27 _ (by rfl)
  have c9r9892_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r9892targets : Array (List GridPoint) := #[[(0,5),(1,5),(2,5),(3,4),(3,5),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,4),(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(0,6),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,4),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(1,6),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(2,0),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(2,1),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(2,2),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,5),(1,5),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,6),(1,6),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r9892choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9892targets [(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r9892choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9892targets, c9r9892choice, ?_, checked⟩
    intro S h
    simp only [c9r9892targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 6 _ (by rfl)
  have c9r9893_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r9893targets : Array (List GridPoint) := #[[(0,5),(1,5),(2,5),(3,5),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,4),(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(0,6),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,4),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(1,6),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(2,0),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(2,1),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(2,2),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(2,3),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(1,5),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,6),(1,6),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r9893choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (11,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c9r9893targets [(0,5),(1,5),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] c9r9893choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9893targets, c9r9893choice, ?_, checked⟩
    intro S h
    simp only [c9r9893targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 18 _ (by rfl)
  have c9r9894_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c9r9894targets : Array (List GridPoint) := #[[(0,6),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,7),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,4),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,6),(0,7),(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,7),(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c9r9894choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 7) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 8) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r9894targets [(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c9r9894choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9894targets, c9r9894choice, ?_, checked⟩
    intro S h
    simp only [c9r9894targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 0 _ (by rfl)
  have c9r9895_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)] := by
    let c9r9895targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)]]
    let c9r9895choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r9895targets [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)] c9r9895choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9895targets, c9r9895choice, ?_, checked⟩
    intro S h
    simp only [c9r9895targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9888_closed
  · subst row; exact c9r9889_closed
  · subst row; exact c9r9890_closed
  · subst row; exact c9r9891_closed
  · subst row; exact c9r9892_closed
  · subst row; exact c9r9893_closed
  · subst row; exact c9r9894_closed
  · subst row; exact c9r9895_closed
theorem C9R09888G1 (row : List GridPoint) (h : row ∈ [[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9896_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)] := by
    let c9r9896targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,7),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)]]
    let c9r9896choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r9896targets [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)] c9r9896choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9896targets, c9r9896choice, ?_, checked⟩
    intro S h
    simp only [c9r9896targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 22 _ (by rfl)
  have c9r9897_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)] := by
    let c9r9897targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)]]
    let c9r9897choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9897targets [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)] c9r9897choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9897targets, c9r9897choice, ?_, checked⟩
    intro S h
    simp only [c9r9897targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 28 _ (by rfl)
  have c9r9898_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)] := by
    let c9r9898targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)]]
    let c9r9898choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9898targets [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)] c9r9898choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9898targets, c9r9898choice, ?_, checked⟩
    intro S h
    simp only [c9r9898targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 1 _ (by rfl)
  have c9r9899_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)] := by
    let c9r9899targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)]]
    let c9r9899choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9899targets [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)] c9r9899choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9899targets, c9r9899choice, ?_, checked⟩
    intro S h
    simp only [c9r9899targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 5 _ (by rfl)
  have c9r9900_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)] := by
    let c9r9900targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)]]
    let c9r9900choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9900targets [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)] c9r9900choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9900targets, c9r9900choice, ?_, checked⟩
    intro S h
    simp only [c9r9900targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 8 _ (by rfl)
  have c9r9901_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)] := by
    let c9r9901targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)]]
    let c9r9901choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9901targets [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)] c9r9901choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9901targets, c9r9901choice, ?_, checked⟩
    intro S h
    simp only [c9r9901targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 10 _ (by rfl)
  have c9r9902_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)] := by
    let c9r9902targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)]]
    let c9r9902choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r9902targets [(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)] c9r9902choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9902targets, c9r9902choice, ?_, checked⟩
    intro S h
    simp only [c9r9902targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 12 _ (by rfl)
  have c9r9903_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)] := by
    let c9r9903targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1)],[(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,2),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,3),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,4),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,6),(0,7),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,3)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,4)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,5)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,6)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(3,0)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(3,1)]]
    let c9r9903choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9903targets [(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)] c9r9903choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9903targets, c9r9903choice, ?_, checked⟩
    intro S h
    simp only [c9r9903targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9896_closed
  · subst row; exact c9r9897_closed
  · subst row; exact c9r9898_closed
  · subst row; exact c9r9899_closed
  · subst row; exact c9r9900_closed
  · subst row; exact c9r9901_closed
  · subst row; exact c9r9902_closed
  · subst row; exact c9r9903_closed
theorem C9R09888G2 (row : List GridPoint) (h : row ∈ [[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9904_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)] := by
    let c9r9904targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2)],[(0,2),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,3),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,4),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,6),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2)],[(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,4)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,5)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,6)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,0)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,1)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,2)]]
    let c9r9904choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9904targets [(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)] c9r9904choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9904targets, c9r9904choice, ?_, checked⟩
    intro S h
    simp only [c9r9904targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 16 _ (by rfl)
  have c9r9905_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r9905targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,5),(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,6),(0,7),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,6),(1,0),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,6),(1,1),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,6),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,7),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,6)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r9905choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9905targets [(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)] c9r9905choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9905targets, c9r9905choice, ?_, checked⟩
    intro S h
    simp only [c9r9905targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 29 _ (by rfl)
  have c9r9906_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r9906targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,5),(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(0,7),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,0),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,1),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,2),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,7),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,6)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r9906choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9906targets [(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r9906choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9906targets, c9r9906choice, ?_, checked⟩
    intro S h
    simp only [c9r9906targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 10 _ (by rfl)
  have c9r9907_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r9907targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,5),(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(0,7),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,0),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,1),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,2),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,3),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,7),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r9907choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9907targets [(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r9907choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9907targets, c9r9907choice, ?_, checked⟩
    intro S h
    simp only [c9r9907targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 23 _ (by rfl)
  have c9r9908_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r9908targets : Array (List GridPoint) := #[[(0,6),(1,6),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,5),(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(0,7),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,0),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,1),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,2),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,3),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,4),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,7),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r9908choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c9r9908targets [(0,6),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] c9r9908choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9908targets, c9r9908choice, ?_, checked⟩
    intro S h
    simp only [c9r9908targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 5 _ (by rfl)
  have c9r9909_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)] := by
    let c9r9909targets : Array (List GridPoint) := #[[(0,7),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,1),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,2),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,3),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,4),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,5),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,7),(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)]]
    let c9r9909choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 8) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (16,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c9r9909targets [(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)] c9r9909choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9909targets, c9r9909choice, ?_, checked⟩
    intro S h
    simp only [c9r9909targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h
  · subst row; exact c9r9904_closed
  · subst row; exact c9r9905_closed
  · subst row; exact c9r9906_closed
  · subst row; exact c9r9907_closed
  · subst row; exact c9r9908_closed
  · subst row; exact c9r9909_closed
theorem C9R09888_closed (row : List GridPoint) (h : FamilyMember row F9B004L53) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L53, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R09888G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09888G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09888G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09888G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09888G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09888G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09888G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09888G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09888G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09888G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09888G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09888G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09888G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09888G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09888G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09888G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09888G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09888G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09888G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09888G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09888G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09888G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
end Polyomino57
