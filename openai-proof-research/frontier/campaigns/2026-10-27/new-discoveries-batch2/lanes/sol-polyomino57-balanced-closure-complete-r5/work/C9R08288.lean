import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08288G0 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8288_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c9r8288targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,6),(2,0),(2,1)],[(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c9r8288choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8288targets [(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1)] c9r8288choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8288targets, c9r8288choice, ?_, checked⟩
    intro S h
    simp only [c9r8288targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 7 _ (by rfl)
  have c9r8289_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c9r8289targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,6),(2,0),(2,1),(2,2)],[(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c9r8289choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8289targets [(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2)] c9r8289choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8289targets, c9r8289choice, ?_, checked⟩
    intro S h
    simp only [c9r8289targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 16 _ (by rfl)
  have c9r8290_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r8290targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,3),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(0,6),(0,7),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r8290choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8290targets [(0,3),(0,4),(0,5),(0,6),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r8290choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8290targets, c9r8290choice, ?_, checked⟩
    intro S h
    simp only [c9r8290targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 26 _ (by rfl)
  have c9r8291_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c9r8291targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c9r8291choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8291targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c9r8291choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8291targets, c9r8291choice, ?_, checked⟩
    intro S h
    simp only [c9r8291targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 5 _ (by rfl)
  have c9r8292_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c9r8292targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c9r8292choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8292targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c9r8292choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8292targets, c9r8292choice, ?_, checked⟩
    intro S h
    simp only [c9r8292targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 10 _ (by rfl)
  have c9r8293_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c9r8293targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c9r8293choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8293targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c9r8293choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8293targets, c9r8293choice, ?_, checked⟩
    intro S h
    simp only [c9r8293targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 14 _ (by rfl)
  have c9r8294_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c9r8294targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c9r8294choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8294targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c9r8294choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8294targets, c9r8294choice, ?_, checked⟩
    intro S h
    simp only [c9r8294targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 17 _ (by rfl)
  have c9r8295_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c9r8295targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c9r8295choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8295targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c9r8295choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8295targets, c9r8295choice, ?_, checked⟩
    intro S h
    simp only [c9r8295targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8288_closed
  · subst row; exact c9r8289_closed
  · subst row; exact c9r8290_closed
  · subst row; exact c9r8291_closed
  · subst row; exact c9r8292_closed
  · subst row; exact c9r8293_closed
  · subst row; exact c9r8294_closed
  · subst row; exact c9r8295_closed
theorem C9R08288G1 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8296_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c9r8296targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c9r8296choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8296targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c9r8296choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8296targets, c9r8296choice, ?_, checked⟩
    intro S h
    simp only [c9r8296targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 21 _ (by rfl)
  have c9r8297_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)] := by
    let c9r8297targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(2,6)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(2,6)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(2,6)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(1,7)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(1,7)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,6)]]
    let c9r8297choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8297targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)] c9r8297choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8297targets, c9r8297choice, ?_, checked⟩
    intro S h
    simp only [c9r8297targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 28 _ (by rfl)
  have c9r8298_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)] := by
    let c9r8298targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,0)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,0)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,0)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,0)],[(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(1,6),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(3,0)]]
    let c9r8298choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8298targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)] c9r8298choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8298targets, c9r8298choice, ?_, checked⟩
    intro S h
    simp only [c9r8298targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 1 _ (by rfl)
  have c9r8299_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)] := by
    let c9r8299targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,1)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,1)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,1)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(3,1)]]
    let c9r8299choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8299targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)] c9r8299choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8299targets, c9r8299choice, ?_, checked⟩
    intro S h
    simp only [c9r8299targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 5 _ (by rfl)
  have c9r8300_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)] := by
    let c9r8300targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,2)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,2)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(3,2)]]
    let c9r8300choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8300targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)] c9r8300choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8300targets, c9r8300choice, ?_, checked⟩
    intro S h
    simp only [c9r8300targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 8 _ (by rfl)
  have c9r8301_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)] := by
    let c9r8301targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(3,3)]]
    let c9r8301choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8301targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)] c9r8301choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8301targets, c9r8301choice, ?_, checked⟩
    intro S h
    simp only [c9r8301targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 11 _ (by rfl)
  have c9r8302_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)] := by
    let c9r8302targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,5)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,5)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,5)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6),(2,6)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5),(2,6)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5),(3,5)]]
    let c9r8302choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8302targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)] c9r8302choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8302targets, c9r8302choice, ?_, checked⟩
    intro S h
    simp only [c9r8302targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 14 _ (by rfl)
  have c9r8303_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c9r8303targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c9r8303choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8303targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] c9r8303choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8303targets, c9r8303choice, ?_, checked⟩
    intro S h
    simp only [c9r8303targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 18 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8296_closed
  · subst row; exact c9r8297_closed
  · subst row; exact c9r8298_closed
  · subst row; exact c9r8299_closed
  · subst row; exact c9r8300_closed
  · subst row; exact c9r8301_closed
  · subst row; exact c9r8302_closed
  · subst row; exact c9r8303_closed
theorem C9R08288G2 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8304_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] := by
    let c9r8304targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,2)],[(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
    let c9r8304choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8304targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] c9r8304choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8304targets, c9r8304choice, ?_, checked⟩
    intro S h
    simp only [c9r8304targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 21 _ (by rfl)
  have c9r8305_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] := by
    let c9r8305targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,3)],[(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
    let c9r8305choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8305targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] c9r8305choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8305targets, c9r8305choice, ?_, checked⟩
    intro S h
    simp only [c9r8305targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 24 _ (by rfl)
  have c9r8306_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] := by
    let c9r8306targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(3,0)],[(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
    let c9r8306choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8306targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] c9r8306choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8306targets, c9r8306choice, ?_, checked⟩
    intro S h
    simp only [c9r8306targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 26 _ (by rfl)
  have c9r8307_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c9r8307targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c9r8307choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8307targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] c9r8307choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8307targets, c9r8307choice, ?_, checked⟩
    intro S h
    simp only [c9r8307targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 29 _ (by rfl)
  have c9r8308_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c9r8308targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c9r8308choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8308targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] c9r8308choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8308targets, c9r8308choice, ?_, checked⟩
    intro S h
    simp only [c9r8308targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 0 _ (by rfl)
  have c9r8309_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c9r8309targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c9r8309choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8309targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] c9r8309choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8309targets, c9r8309choice, ?_, checked⟩
    intro S h
    simp only [c9r8309targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 3 _ (by rfl)
  have c9r8310_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c9r8310targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c9r8310choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8310targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] c9r8310choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8310targets, c9r8310choice, ?_, checked⟩
    intro S h
    simp only [c9r8310targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 6 _ (by rfl)
  have c9r8311_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c9r8311targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c9r8311choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8311targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] c9r8311choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8311targets, c9r8311choice, ?_, checked⟩
    intro S h
    simp only [c9r8311targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8304_closed
  · subst row; exact c9r8305_closed
  · subst row; exact c9r8306_closed
  · subst row; exact c9r8307_closed
  · subst row; exact c9r8308_closed
  · subst row; exact c9r8309_closed
  · subst row; exact c9r8310_closed
  · subst row; exact c9r8311_closed
theorem C9R08288G3 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8312_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] := by
    let c9r8312targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c9r8312choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8312targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] c9r8312choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8312targets, c9r8312choice, ?_, checked⟩
    intro S h
    simp only [c9r8312targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 12 _ (by rfl)
  have c9r8313_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] := by
    let c9r8313targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c9r8313choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8313targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] c9r8313choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8313targets, c9r8313choice, ?_, checked⟩
    intro S h
    simp only [c9r8313targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 15 _ (by rfl)
  have c9r8314_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] := by
    let c9r8314targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c9r8314choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8314targets [(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] c9r8314choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8314targets, c9r8314choice, ?_, checked⟩
    intro S h
    simp only [c9r8314targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 23 _ (by rfl)
  have c9r8315_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c9r8315targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,4),(0,5),(0,6),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c9r8315choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8315targets [(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] c9r8315choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8315targets, c9r8315choice, ?_, checked⟩
    intro S h
    simp only [c9r8315targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 30 _ (by rfl)
  have c9r8316_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r8316targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(0,6),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r8316choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8316targets [(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r8316choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8316targets, c9r8316choice, ?_, checked⟩
    intro S h
    simp only [c9r8316targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 5 _ (by rfl)
  have c9r8317_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c9r8317targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c9r8317choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8317targets [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c9r8317choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8317targets, c9r8317choice, ?_, checked⟩
    intro S h
    simp only [c9r8317targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 12 _ (by rfl)
  have c9r8318_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)] := by
    let c9r8318targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5),(3,0),(3,1)],[(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5),(3,0),(3,1)],[(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5),(3,0),(3,1)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(1,6),(2,0),(2,1)],[(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(2,5)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(3,1)]]
    let c9r8318choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8318targets [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1)] c9r8318choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8318targets, c9r8318choice, ?_, checked⟩
    intro S h
    simp only [c9r8318targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 19 _ (by rfl)
  have c9r8319_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c9r8319targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(2,2)],[(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c9r8319choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8319targets [(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] c9r8319choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8319targets, c9r8319choice, ?_, checked⟩
    intro S h
    simp only [c9r8319targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8312_closed
  · subst row; exact c9r8313_closed
  · subst row; exact c9r8314_closed
  · subst row; exact c9r8315_closed
  · subst row; exact c9r8316_closed
  · subst row; exact c9r8317_closed
  · subst row; exact c9r8318_closed
  · subst row; exact c9r8319_closed
theorem C9R08288_closed (row : List GridPoint) (h : FamilyMember row F9B004L3) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L3, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08288G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08288G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08288G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08288G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08288G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08288G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08288G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08288G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08288G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08288G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08288G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08288G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08288G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08288G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08288G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08288G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08288G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08288G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08288G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08288G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08288G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08288G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08288G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08288G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08288G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08288G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08288G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08288G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08288G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08288G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08288G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08288G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
